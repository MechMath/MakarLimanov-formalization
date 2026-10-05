import MakarLimanov.FiniteNewtonInduction

/-! A finite sum with a nonzero positive homogeneous component cannot be a unit. -/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.HomogeneousSum

open MvPolynomial

noncomputable section

variable {σ F : Type*} [Field F]

theorem nonunit_of_nonzero_positive_component
    (S : Finset ℕ) (P : ℕ → MvPolynomial σ F)
    (hhom : ∀ j ∈ S, (P j).IsHomogeneous j)
    (hpos : ∃ j ∈ S, 0 < j ∧ P j ≠ 0) :
    ¬ IsUnit (∑ j ∈ S, P j) := by
  obtain ⟨j, hjS, hjpos, hj0⟩ := hpos
  have hjcoeff : (P j).coeff ≠ 0 := by
    intro h
    apply hj0
    apply AddMonoidAlgebra.coeff_injective
    simpa using h
  obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr hjcoeff
  have hdcoef : (P j).coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  have hother : ∀ l ∈ S, l ≠ j → (P l).coeff d = 0 := by
    intro l hl hlj
    by_contra hne
    have hld : d.degree = l := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom l hl hne
    have hjd : d.degree = j := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom j hjS hdcoef
    omega
  have hsumcoef : (∑ l ∈ S, P l).coeff d ≠ 0 := by
    rw [coeff_sum]
    rw [Finset.sum_eq_single j]
    · simpa using hdcoef
    · intro l hl hlj
      exact hother l hl hlj
    · intro hnot
      exact (hnot hjS).elim
  have hsum0 : (∑ l ∈ S, P l) ≠ 0 := by
    intro hzero
    apply hsumcoef
    simp only [hzero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  intro hunit
  have hdeg : (∑ l ∈ S, P l).totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have hhom0 : (∑ l ∈ S, P l).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_of_totalDegree_zero σ hdeg
  have hsd : d.degree = 0 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom0 hsumcoef
  have hjd : d.degree = j := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom j hjS hdcoef
  omega

end
end MakarLimanov.HomogeneousSum
