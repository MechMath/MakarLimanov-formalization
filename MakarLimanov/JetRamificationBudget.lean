import MakarLimanov.Ramification
import MakarLimanov.FiniteJets

/-!
# Ramification budget for finite mixed-jet triangles

The radial argument used for finite coordinate sets applies directly to a jet
triangle.  The only bookkeeping needed is an equivalence between that finite
triangle and `Fin d`; total degree, constant coefficient, divisibility, and
sparse support are all preserved by the corresponding polynomial equivalence.
-/

namespace MakarLimanov.JetRamificationBudget

open MvPolynomial NewtonCKRoot

noncomputable section

variable {F : Type*} [Field F] [CharZero F]

theorem factor_degree_budget_triangle {N : ℕ}
    (Ψ P : MvPolynomial (Triangle N) F) (e m : ℕ) (he : 0 < e)
    (h0 : MvPolynomial.constantCoeff Ψ ≠ 0)
    (hs : ∀ s ∈ Ψ.support, e ∣ s.sum (fun _ n ↦ n))
    (hP : ¬ IsUnit P) (hm : P ^ m ∣ Ψ) :
    e * m ≤ Ψ.totalDegree := by
  let f : Triangle N → Fin (N + 1) × Fin (N + 1) := fun ij ↦
    (⟨ij.val.1, by have := ij.property; omega⟩,
      ⟨ij.val.2, by have := ij.property; omega⟩)
  letI : Finite (Triangle N) := Finite.of_injective f (by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Fin.val (congrArg Prod.fst hab)
    · exact congrArg Fin.val (congrArg Prod.snd hab))
  letI : Fintype (Triangle N) := Fintype.ofFinite (Triangle N)
  let d := Fintype.card (Triangle N)
  let eqv : Triangle N ≃ Fin d := Fintype.equivFin (Triangle N)
  let ρ : MvPolynomial (Triangle N) F ≃ₐ[F] MvPolynomial (Fin d) F :=
    MvPolynomial.renameEquiv F eqv
  let Ψ' := ρ Ψ
  let P' := ρ P
  have h0' : MvPolynomial.constantCoeff Ψ' ≠ 0 := by
    simpa [Ψ', ρ, MvPolynomial.constantCoeff_rename] using h0
  have hs' : ∀ s ∈ Ψ'.support, e ∣ s.sum (fun _ n ↦ n) := by
    intro s hs_mem
    have hsupport : s ∈ (MvPolynomial.rename eqv Ψ).support := by
      simpa [Ψ', ρ, MvPolynomial.renameEquiv_apply] using hs_mem
    rw [MvPolynomial.support_rename_of_injective eqv.injective] at hsupport
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsupport
    have hts := hs t ht
    simpa only [Finsupp.sum_mapDomain_index_inj eqv.injective] using hts
  have hP' : ¬ IsUnit P' := by
    intro h
    apply hP
    have hi := h.map (ρ.symm : MvPolynomial (Fin d) F →* MvPolynomial (Triangle N) F)
    simpa [P', ρ] using hi
  have hm' : P' ^ m ∣ Ψ' := by
    obtain ⟨Q, hQ⟩ := hm
    refine ⟨ρ Q, ?_⟩
    simpa [Ψ', P', ρ, hQ] using congrArg ρ hQ
  have hbound := Ramification.factor_degree_budget_general Ψ' P' e m he h0' hs' hP' hm'
  calc
    e * m ≤ Ψ'.totalDegree := hbound
    _ = Ψ.totalDegree := by
      dsimp [Ψ', ρ]
      exact MvPolynomial.totalDegree_renameEquiv eqv Ψ

end

end MakarLimanov.JetRamificationBudget
