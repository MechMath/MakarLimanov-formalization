import MakarLimanov.GeneralNewtonRoot
import MakarLimanov.SparseFactorBudget

/-!
# A differential Newton root with its ramification budget

The factor used to construct the root is the same exact factor whose
multiplicity satisfies the sparse degree bound. Thus the first nonzero
homogeneous term after translation retains the certified budget.
-/

noncomputable section

namespace MakarLimanov.SparseNewtonRoot

open MvPolynomial NewtonCKRoot FiniteJets

universe u

variable {k F : Type u} [Field k] [Field F] [CharZero k] [CharZero F] [Algebra k F]

/-- Lemmas 8 and 9 together: the differential correction has a first nonzero
translated component of degree `m`, and this very `m` obeys `e*m ≤ deg Ψ`. -/
theorem exists_polynomial_step_with_budget
    (Ψ : MvPolynomial (ℕ × ℕ) F) (e : ℕ) (he : 0 < e)
    (hconst : constantCoeff Ψ ≠ 0)
    (hsparse : ∀ d ∈ Ψ.support, e ∣ d.degree)
    (hΨ : ¬ IsUnit Ψ)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) :
    ∃ m : ℕ, 0 < m ∧ e * m ≤ Ψ.totalDegree ∧
      ∃ (G : Type u) (_ : Field G) (_ : Algebra k G) (_ : Algebra F G)
        (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (v : G),
        Function.Commute D H ∧
        (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
        (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
        (let jets : ℕ × ℕ → G := fun ij ↦ D^[ij.1] (H^[ij.2] v)
        let translated := NewtonTranslation.translate jets (MvPolynomial.map (algebraMap F G) Ψ)
        MvPolynomial.aeval jets Ψ = 0 ∧
        (∀ j < m, homogeneousComponent j translated = 0) ∧
        homogeneousComponent m translated ≠ 0) := by
  obtain ⟨P, Q, m, hP, hm, heq, hnd, horderP, horderQ, hbudget⟩ :=
    SparseFactorBudget.exists_factorisation_with_sparse_budget Ψ e he hconst hsparse hΨ
  let N := differentialOrder Ψ
  obtain ⟨P', hP'⟩ := exists_triangle P N horderP.le
  obtain ⟨Q', hQ'⟩ := exists_triangle Q N (horderQ.trans horderP.le)
  have hPirr : Irreducible P' := by
    rw [← includeTriangle_irreducible_iff, hP']
    exact hP
  have horder : differentialOrder (includeTriangle N P') = N := by
    rw [hP']
    exact horderP
  have hnd' : ¬ P' ∣ Q' := by
    rw [← includeTriangle_dvd_iff, hP', hQ']
    exact hnd
  obtain ⟨G, hG, hkG, hFG, hkFG, D, H, v, hDH, hD, hH,
      hroot, ⟨ij, hsep⟩, hker⟩ :=
    GeneralNewtonRoot.exists_differential_factor_root P' hPirr horder δ η hc
  let jets : ℕ × ℕ → G := fun ij ↦ D^[ij.1] (H^[ij.2] v)
  have hp : MvPolynomial.aeval jets P = 0 := by
    rw [← hP', aeval_includeTriangle]
    exact hroot
  have hq : MvPolynomial.aeval jets Q ≠ 0 := by
    rw [← hQ', aeval_includeTriangle]
    exact fun hz ↦ hnd' ((hker Q').mp hz)
  have hsepP : MvPolynomial.aeval jets (pderiv ij.val P) ≠ 0 := by
    rw [← hP']
    change MvPolynomial.aeval jets
      (pderiv ij.val (MvPolynomial.rename Subtype.val P')) ≠ 0
    rw [pderiv_rename Subtype.val_injective, MvPolynomial.aeval_rename]
    exact hsep
  have hev (A : MvPolynomial (ℕ × ℕ) F) :
      MvPolynomial.eval jets (MvPolynomial.map (algebraMap F G) A) =
        MvPolynomial.aeval jets A := by
    rw [MvPolynomial.eval_map]
    rfl
  have hlow := NewtonTranslation.translated_factor_lowest_term jets
    (MvPolynomial.map (algebraMap F G) P) (MvPolynomial.map (algebraMap F G) Q)
    m ij.val (by rwa [hev]) (by rwa [hev]) (by rwa [pderiv_map, hev])
  refine ⟨m, hm, hbudget, G, hG, hkG, hFG, hkFG, D, H, v, hDH, hD, hH, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change MvPolynomial.aeval jets Ψ = 0
    rw [heq, map_mul, map_pow, hp, zero_pow (Nat.ne_of_gt hm), zero_mul]
  · simpa only [heq, map_mul, map_pow] using hlow.1
  · simpa only [heq, map_mul, map_pow] using hlow.2.2

end MakarLimanov.SparseNewtonRoot
