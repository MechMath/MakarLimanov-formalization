import MakarLimanov.NewtonCKRoot
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Finite triangular presentations of differential polynomials

Every polynomial in the full mixed-jet ring belongs to a finite triangle of jets.
The differential order measures the largest sum of the two derivative indices
which actually occurs.  These presentations retain divisibility and irreducibility
and commute with evaluation at the mixed jets of a differential element.
-/

namespace MakarLimanov.FiniteJets

open MvPolynomial NewtonCKRoot

noncomputable section

variable {F : Type*} [Field F]

/-- The largest total derivative index occurring in the finite variable support. -/
def differentialOrder (P : MvPolynomial (ℕ × ℕ) F) : ℕ :=
  P.vars.sup (fun ij ↦ ij.1 + ij.2)

theorem le_differentialOrder (P : MvPolynomial (ℕ × ℕ) F)
    {ij : ℕ × ℕ} (hij : ij ∈ P.vars) : ij.1 + ij.2 ≤ differentialOrder P :=
  Finset.le_sup (f := fun ij : ℕ × ℕ ↦ ij.1 + ij.2) hij

@[simp] theorem differentialOrder_C (c : F) :
    differentialOrder (C c : MvPolynomial (ℕ × ℕ) F) = 0 := by
  simp [differentialOrder]

theorem differentialOrder_of_isUnit {P : MvPolynomial (ℕ × ℕ) F}
    (hP : IsUnit P) : differentialOrder P = 0 := by
  obtain ⟨c, _, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hP
  exact differentialOrder_C c

/-- A nonzero product has exactly the maximum differential order of its two factors. -/
theorem differentialOrder_mul {P Q : MvPolynomial (ℕ × ℕ) F}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    differentialOrder (P * Q) = max (differentialOrder P) (differentialOrder Q) := by
  simp only [differentialOrder, GenericKernel.vars_mul_eq P Q hP hQ, Finset.sup_union]

/-- A nonconstant nonzero jet polynomial has an irreducible factor of the same
differential order.  This makes the maximal-order factor selection in Section 5 explicit. -/
theorem exists_irreducible_factor_of_order (P : MvPolynomial (ℕ × ℕ) F)
    (hP : ¬ IsUnit P) (hP0 : P ≠ 0) :
    ∃ Q : MvPolynomial (ℕ × ℕ) F,
      Irreducible Q ∧ Q ∣ P ∧ differentialOrder Q = differentialOrder P := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hP0 rfl).elim
  | unit P hunit => exact (hP hunit).elim
  | mul A B hA hB ih =>
    rw [differentialOrder_mul hB.ne_zero hA]
    by_cases hunit : IsUnit A
    · refine ⟨B, hB, dvd_mul_right B A, ?_⟩
      rw [differentialOrder_of_isUnit hunit, max_eq_left (Nat.zero_le _)]
    · obtain ⟨Q, hQ, hQA, horder⟩ := ih hunit hA
      by_cases hle : differentialOrder B ≤ differentialOrder A
      · exact ⟨Q, hQ, hQA.trans (dvd_mul_left A B), by rw [max_eq_right hle, horder]⟩
      · exact ⟨B, hB, dvd_mul_right B A, by rw [max_eq_left (le_of_not_ge hle)]⟩

/-- Include a finite jet triangle in the full mixed-jet ring. -/
def includeTriangle (N : ℕ) :
    MvPolynomial (Triangle N) F →ₐ[F] MvPolynomial (ℕ × ℕ) F :=
  rename Subtype.val

theorem includeTriangle_injective (N : ℕ) :
    Function.Injective (includeTriangle (F := F) N) :=
  MvPolynomial.rename_injective _ Subtype.val_injective

/-- Any differential-order bound produces a polynomial in the corresponding triangle. -/
theorem exists_triangle (P : MvPolynomial (ℕ × ℕ) F) (N : ℕ)
    (hN : differentialOrder P ≤ N) :
    ∃ Q : MvPolynomial (Triangle N) F, includeTriangle N Q = P := by
  apply MvPolynomial.exists_rename_eq_of_vars_subset_range P Subtype.val
    Subtype.val_injective
  intro ij hij
  exact ⟨⟨ij, (le_differentialOrder P hij).trans hN⟩, rfl⟩

/-- Restriction to the smallest triangle containing the variables of the polynomial. -/
def trianglePolynomial (P : MvPolynomial (ℕ × ℕ) F) :
    MvPolynomial (Triangle (differentialOrder P)) F :=
  Classical.choose (exists_triangle P (differentialOrder P) le_rfl)

@[simp] theorem include_trianglePolynomial (P : MvPolynomial (ℕ × ℕ) F) :
    includeTriangle (differentialOrder P) (trianglePolynomial P) = P :=
  Classical.choose_spec (exists_triangle P (differentialOrder P) le_rfl)

/-- Enlarging a finite jet ring does not introduce divisibility. -/
theorem includeTriangle_dvd_iff {N : ℕ} (P Q : MvPolynomial (Triangle N) F) :
    includeTriangle N P ∣ includeTriangle N Q ↔ P ∣ Q :=
  GenericKernel.rename_dvd_iff _ Subtype.val_injective P Q

/-- Irreducibility is unchanged by adjoining the jets outside the triangle. -/
theorem includeTriangle_irreducible_iff {N : ℕ} (P : MvPolynomial (Triangle N) F) :
    Irreducible (includeTriangle N P) ↔ Irreducible P := by
  constructor
  · intro hP
    refine ⟨fun h ↦ hP.not_isUnit (h.map (includeTriangle N).toRingHom), ?_⟩
    intro A B hAB
    have hm : includeTriangle N P = includeTriangle N A * includeTriangle N B := by
      rw [hAB, map_mul]
    rcases hP.isUnit_or_isUnit hm with hA | hB
    · left
      have h := hA.map (MvPolynomial.killCompl
        (f := (Subtype.val : Triangle N → ℕ × ℕ)) Subtype.val_injective).toRingHom
      simpa only [includeTriangle, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.killCompl_rename_app] using h
    · right
      have h := hB.map (MvPolynomial.killCompl
        (f := (Subtype.val : Triangle N → ℕ × ℕ)) Subtype.val_injective).toRingHom
      simpa only [includeTriangle, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.killCompl_rename_app] using h
  · exact GenericKernel.irreducible_rename Subtype.val Subtype.val_injective

/-- The canonical finite presentation of an irreducible jet polynomial is irreducible. -/
theorem trianglePolynomial_irreducible {P : MvPolynomial (ℕ × ℕ) F}
    (hP : Irreducible P) : Irreducible (trianglePolynomial P) := by
  rw [← includeTriangle_irreducible_iff, include_trianglePolynomial]
  exact hP

/-- A factor of a nonzero polynomial has no variables of larger differential order. -/
theorem differentialOrder_le_of_dvd {P Q : MvPolynomial (ℕ × ℕ) F}
    (hPQ : P ∣ Q) (hQ : Q ≠ 0) : differentialOrder P ≤ differentialOrder Q := by
  obtain ⟨R, rfl⟩ := hPQ
  have hP : P ≠ 0 := left_ne_zero_of_mul hQ
  have hR : R ≠ 0 := right_ne_zero_of_mul hQ
  apply Finset.sup_le
  intro ij hij
  apply le_differentialOrder
  rw [GenericKernel.vars_mul_eq P R hP hR]
  exact Finset.mem_union_left _ hij

/-- Select an irreducible factor of maximal differential order with its exact
positive multiplicity.  The cofactor uses no higher-order jets than the chosen factor. -/
theorem exists_exact_factorization (Ψ : MvPolynomial (ℕ × ℕ) F)
    (hΨ : ¬ IsUnit Ψ) (hΨ0 : Ψ ≠ 0) :
    ∃ (P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Irreducible P ∧ 0 < m ∧ Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder Ψ ∧
      differentialOrder Q ≤ differentialOrder P := by
  obtain ⟨P, hP, hPΨ, horder⟩ := exists_irreducible_factor_of_order Ψ hΨ hΨ0
  have hfinite : FiniteMultiplicity P Ψ := .of_not_isUnit hP.not_isUnit hΨ0
  obtain ⟨Q, heq, hQ⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  have hm : 0 < multiplicity P Ψ :=
    Nat.pos_of_ne_zero (multiplicity_ne_zero.mpr hPΨ)
  refine ⟨P, Q, multiplicity P Ψ, hP, hm, heq, hQ, horder, ?_⟩
  rw [horder]
  apply differentialOrder_le_of_dvd _ hΨ0
  rw [heq]
  exact dvd_mul_left Q _

/-- Nonzero constant term is inherited by both parts of the exact factorization. -/
theorem constantCoeff_factors_ne_zero {Ψ P Q : MvPolynomial (ℕ × ℕ) F} {m : ℕ}
    (hΨ : constantCoeff Ψ ≠ 0) (hPΨ : P ∣ Ψ) (heq : Ψ = P ^ m * Q) :
    constantCoeff P ≠ 0 ∧ constantCoeff Q ≠ 0 := by
  constructor
  · exact ne_zero_of_dvd_ne_zero hΨ (map_dvd constantCoeff hPΨ)
  · have hQΨ : Q ∣ Ψ := by rw [heq]; exact dvd_mul_left Q _
    exact ne_zero_of_dvd_ne_zero hΨ (map_dvd constantCoeff hQΨ)

/-- The factor and cofactor fit in the same triangle as their nonzero product. -/
theorem exists_triangle_factors (P Q : MvPolynomial (ℕ × ℕ) F) (hPQ : P * Q ≠ 0) :
    ∃ P' Q' : MvPolynomial (Triangle (differentialOrder (P * Q))) F,
      includeTriangle _ P' = P ∧ includeTriangle _ Q' = Q ∧
      includeTriangle _ (P' * Q') = P * Q := by
  obtain ⟨P', hP'⟩ := exists_triangle P _
    (differentialOrder_le_of_dvd (dvd_mul_right P Q) hPQ)
  obtain ⟨Q', hQ'⟩ := exists_triangle Q _
    (differentialOrder_le_of_dvd (dvd_mul_left Q P) hPQ)
  exact ⟨P', Q', hP', hQ', by rw [map_mul, hP', hQ']⟩

/-- The maximal-order factor and its exact cofactor can both be selected inside
one finite triangle, with irreducibility and the nondivisibility assertion retained. -/
theorem exists_triangle_exact_factorization (Ψ : MvPolynomial (ℕ × ℕ) F)
    (hΨ : ¬ IsUnit Ψ) (hΨ0 : Ψ ≠ 0) :
    ∃ (P Q : MvPolynomial (Triangle (differentialOrder Ψ)) F) (m : ℕ),
      Irreducible P ∧ 0 < m ∧ Ψ = includeTriangle _ (P ^ m * Q) ∧ ¬ P ∣ Q ∧
      differentialOrder (includeTriangle _ P) = differentialOrder Ψ := by
  obtain ⟨P, Q, m, hP, hm, heq, hPQ, horderP, horderQ⟩ :=
    exists_exact_factorization Ψ hΨ hΨ0
  obtain ⟨P', hP'⟩ := exists_triangle P _ horderP.le
  obtain ⟨Q', hQ'⟩ := exists_triangle Q _ (horderQ.trans horderP.le)
  refine ⟨P', Q', m, ?_, hm, ?_, ?_, ?_⟩
  · rw [← includeTriangle_irreducible_iff, hP']
    exact hP
  · rw [map_mul, map_pow, hP', hQ']
    exact heq
  · rw [← includeTriangle_dvd_iff, hP', hQ']
    exact hPQ
  · rw [hP']
    exact horderP

/-- Evaluating a triangular presentation agrees with evaluating the original jet polynomial. -/
theorem aeval_includeTriangle {E : Type*} [CommSemiring E] [Algebra F E]
    {N : ℕ} (x : ℕ × ℕ → E) (P : MvPolynomial (Triangle N) F) :
    MvPolynomial.aeval x (includeTriangle N P) =
      MvPolynomial.aeval (fun ij : Triangle N ↦ x ij.val) P := by
  rw [includeTriangle, MvPolynomial.aeval_rename]
  rfl

end

end MakarLimanov.FiniteJets
