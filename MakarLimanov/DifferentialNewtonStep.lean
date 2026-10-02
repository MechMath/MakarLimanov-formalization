import MakarLimanov.NewtonCKRoot
import MakarLimanov.NewtonTranslation

/-!
# One Newton step with commuting differential jets

The coefficient polynomial in the Newton argument is a polynomial in finitely
many mixed jets.  This file combines the Cauchy--Kowalevski root construction
with the translated homogeneous-component calculation.  Thus the root used by
the step is represented by actual commuting derivations, rather than being an
unstructured point in an algebraic extension.
-/

namespace MakarLimanov.DifferentialNewtonStep

open MvPolynomial NewtonTranslation NewtonCKRoot

noncomputable section

universe u

variable {k F : Type u} [CommRing k] [Field F] [CharZero F] [Algebra k F]
  {N : ℕ}

theorem exists_step (P Q : MvPolynomial (Triangle N) F)
    (hP : Irreducible P) (hdeg : (stripPolynomial P).natDegree ≠ 0)
    (hQ : ¬ P ∣ Q) (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (hN : 0 < N) (m : ℕ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E),
      ∃ (D H : Derivation k E E) (v : E),
        Function.Commute D H ∧
        (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
        (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
        (let jets : Triangle N → E :=
          fun ij ↦ D^[ij.val.1] (H^[ij.val.2] v)
        let translated :=
          translate jets (MvPolynomial.map (algebraMap F E) (P ^ m * Q))
        MvPolynomial.aeval jets P = 0 ∧
        MvPolynomial.aeval jets Q ≠ 0 ∧
        MvPolynomial.aeval jets (pderiv (leader N) P) ≠ 0 ∧
        (∀ j < m, homogeneousComponent j translated = 0) ∧
        homogeneousComponent m translated =
          C (MvPolynomial.aeval jets Q) *
            linearization jets (MvPolynomial.map (algebraMap F E) P) ^ m ∧
        homogeneousComponent m translated ≠ 0) := by
  obtain ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, hroot, hsep, hker⟩ :=
    NewtonCKRoot.exists_differential_factor_root P hP hdeg δ η hc hN
  let jets : Triangle N → E :=
    fun ij ↦ D^[ij.val.1] (H^[ij.val.2] v)
  have hQv : MvPolynomial.aeval jets Q ≠ 0 := by
    intro hz
    apply hQ
    exact (hker Q).mp hz
  have hmap (A : MvPolynomial (Triangle N) F) :
      MvPolynomial.eval jets (MvPolynomial.map (algebraMap F E) A) =
        MvPolynomial.aeval jets A := by
    rw [MvPolynomial.eval_map]
    rfl
  have hroot' : MvPolynomial.eval jets (MvPolynomial.map (algebraMap F E) P) = 0 :=
    (hmap P).trans hroot
  have hQv' : MvPolynomial.eval jets (MvPolynomial.map (algebraMap F E) Q) ≠ 0 := by
    rw [hmap]
    exact hQv
  have hsep' : MvPolynomial.eval jets
      (pderiv (leader N) (MvPolynomial.map (algebraMap F E) P)) ≠ 0 := by
    rw [MvPolynomial.pderiv_map, hmap]
    exact hsep
  have hlowest := translated_factor_lowest_term jets
    (MvPolynomial.map (algebraMap F E) P) (MvPolynomial.map (algebraMap F E) Q)
    m (leader N) hroot' hQv' hsep'
  refine ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, ?_⟩
  refine ⟨hroot, hQv, hsep, ?_⟩
  simpa only [map_mul, map_pow, hmap] using hlowest

end
end MakarLimanov.DifferentialNewtonStep
