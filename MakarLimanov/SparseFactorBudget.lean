import MakarLimanov.FiniteJets
import MakarLimanov.JetRamificationBudget

/-!
# Sparse factor budgets in the full mixed-jet ring

Unlike a homogeneous residual, a general residual representative is a sum of
different homogeneous pieces.  The radial budget only needs the weaker
support hypothesis: every monomial degree is divisible by `e`.
-/

noncomputable section

namespace MakarLimanov.SparseFactorBudget

open MvPolynomial NewtonCKRoot
open MakarLimanov.FiniteJets
open MakarLimanov.JetRamificationBudget

variable {F : Type*} [Field F] [CharZero F]

private theorem totalDegree_include_eq {N : ℕ}
    (P : MvPolynomial (Triangle N) F) :
    (includeTriangle N P).totalDegree = P.totalDegree := by
  apply le_antisymm
  · rw [includeTriangle, MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro d hd
    rw [MvPolynomial.support_rename_of_injective Subtype.val_injective] at hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    simpa only [Finsupp.sum_mapDomain_index_inj Subtype.val_injective] using
      (MvPolynomial.le_totalDegree hs)
  · rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro s hs
    have hmem : Finsupp.mapDomain Subtype.val s ∈
        (includeTriangle N P).support := by
      rw [includeTriangle, MvPolynomial.support_rename_of_injective Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have hle := MvPolynomial.le_totalDegree hmem
    simpa only [Finsupp.sum_mapDomain_index_inj Subtype.val_injective] using hle

/-- A sparse full jet polynomial admits an exact maximal-order factorisation,
and every factor multiplicity is bounded by the sparse degree budget. -/
theorem exists_factorisation_with_sparse_budget
    (Ψ : MvPolynomial (ℕ × ℕ) F) (e : ℕ) (he : 0 < e)
    (h0 : MvPolynomial.constantCoeff Ψ ≠ 0)
    (hs : ∀ d ∈ Ψ.support, e ∣ d.sum (fun _ n ↦ n))
    (hΨ : ¬ IsUnit Ψ) :
    ∃ (P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Irreducible P ∧ 0 < m ∧ Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder Ψ ∧
      differentialOrder Q ≤ differentialOrder P ∧
      e * m ≤ Ψ.totalDegree := by
  have hΨ0 : Ψ ≠ 0 := by
    intro hzero
    apply h0
    rw [hzero]
    simp
  obtain ⟨P, Q, m, hP, hm, hfactor, hPnotdvd, horderP, horderQ⟩ :=
    exists_exact_factorization Ψ hΨ hΨ0
  let N := differentialOrder Ψ
  obtain ⟨P', hP'⟩ := exists_triangle P N horderP.le
  obtain ⟨Q', hQ'⟩ := exists_triangle Q N (horderQ.trans horderP.le)
  have hinc : includeTriangle N (trianglePolynomial Ψ) = Ψ := by
    simpa [N] using (include_trianglePolynomial Ψ)
  have hconst' : MvPolynomial.constantCoeff (trianglePolynomial Ψ) ≠ 0 := by
    have hcc : MvPolynomial.constantCoeff (includeTriangle N (trianglePolynomial Ψ)) =
        MvPolynomial.constantCoeff (trianglePolynomial Ψ) := by
      simp [includeTriangle, MvPolynomial.constantCoeff_rename]
    rw [hinc] at hcc
    rw [← hcc]
    exact h0
  have htri_eq : trianglePolynomial Ψ = P' ^ m * Q' := by
    apply includeTriangle_injective N
    rw [hinc, map_mul, map_pow, hP', hQ', hfactor]
  have hP'nu : ¬ IsUnit P' := by
    intro hu
    apply hP.not_isUnit
    rw [← hP']
    exact hu.map (includeTriangle N).toRingHom
  have hdiv' : P' ^ m ∣ trianglePolynomial Ψ := ⟨Q', htri_eq⟩
  have hs' : ∀ s ∈ (trianglePolynomial Ψ).support,
      e ∣ s.sum (fun _ n ↦ n) := by
    intro s hs_mem
    have hmem : Finsupp.mapDomain Subtype.val s ∈
        (includeTriangle N (trianglePolynomial Ψ)).support := by
      rw [includeTriangle, MvPolynomial.support_rename_of_injective Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨s, hs_mem, rfl⟩
    rw [hinc] at hmem
    have hfull := hs (Finsupp.mapDomain Subtype.val s) hmem
    simpa only [Finsupp.sum_mapDomain_index_inj Subtype.val_injective] using hfull
  have hbudget' := factor_degree_budget_triangle
    (Ψ := trianglePolynomial Ψ) (P := P') e m he hconst' hs' hP'nu hdiv'
  have hdeg : (trianglePolynomial Ψ).totalDegree = Ψ.totalDegree := by
    calc
      (trianglePolynomial Ψ).totalDegree =
          (includeTriangle N (trianglePolynomial Ψ)).totalDegree :=
        (totalDegree_include_eq (trianglePolynomial Ψ)).symm
      _ = Ψ.totalDegree := congrArg MvPolynomial.totalDegree hinc
  have hbudget : e * m ≤ Ψ.totalDegree := by
    exact hdeg ▸ hbudget'
  exact ⟨P, Q, m, hP, hm, hfactor, hPnotdvd, horderP, horderQ, hbudget⟩

end MakarLimanov.SparseFactorBudget
