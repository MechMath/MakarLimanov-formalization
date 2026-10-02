import MakarLimanov.FiniteNewtonInduction
import MakarLimanov.JetRamificationBudget

/-! The homogeneous variation degree gives the sparse support hypothesis used
in the ramification budget. -/

namespace MakarLimanov.HomogeneousRamification

open MvPolynomial NewtonCKRoot JetRamificationBudget
open FiniteNewtonInduction

noncomputable section

variable {F : Type*} [Field F] [CharZero F]

theorem factor_degree_budget_of_homogeneous {N : ℕ}
    (Ψ P : MvPolynomial (Triangle N) F) (j e m : ℕ)
    (hhom : Ψ.IsHomogeneous j) (he : 0 < e) (hej : e ∣ j)
    (h0 : MvPolynomial.constantCoeff Ψ ≠ 0)
    (hP : ¬ IsUnit P) (hm : P ^ m ∣ Ψ) :
    e * m ≤ j := by
  have hs : ∀ s ∈ Ψ.support, e ∣ s.sum (fun _ n ↦ n) := by
    intro s hs
    exact homogeneous_support_divisible hhom hej s hs
  have hbound := factor_degree_budget_triangle Ψ P e m he h0 hs hP hm
  have hdeg : Ψ.totalDegree = j := hhom.totalDegree (by
    intro hzero
    apply h0
    simp [hzero])
  simpa [hdeg] using hbound

end
end MakarLimanov.HomogeneousRamification
