import MakarLimanov.JetDirectionChange
import MakarLimanov.LeaderDegree
import MakarLimanov.ZeroOrderNewtonRoot
import MakarLimanov.DirectionDerivations

/-! Choosing a noncharacteristic direction for every finite irreducible jet equation. -/

namespace MakarLimanov.GeneralNewtonRoot

open MvPolynomial NewtonCKRoot FiniteJets JetDirectionChange

noncomputable section

universe u

variable {k F : Type u} [Field k] [Field F] [CharZero k] [CharZero F] [Algebra k F]

/-- An irreducible equation of its stated positive order has a pure leader after
a base-field change of differential directions. -/
theorem exists_noncharacteristic_change {N : ℕ} (P : MvPolynomial (Triangle N) F)
    (hP : Irreducible P) (horder : differentialOrder (includeTriangle N P) = N)
    (hN : 0 < N) :
    ∃ c : k, Irreducible (change (algebraMap k F c) P) ∧
      (stripPolynomial (change (algebraMap k F c) P)).natDegree ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_change_pderiv_leader_ne_zero (k := k) P horder hN
  exact ⟨c, hP.map (changeEquiv _), stripPolynomial_natDegree_ne_zero_of_pderiv _ hc⟩

/-- Every irreducible jet equation has a generic root in a commuting differential extension,
with no preferred pure derivative assumed in the input. -/
theorem exists_differential_factor_root {N : ℕ} (P : MvPolynomial (Triangle N) F)
    (hP : Irreducible P) (horder : differentialOrder (includeTriangle N P) = N)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E), ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v)) P = 0 ∧
      (∃ ij : Triangle N, MvPolynomial.aeval
        (fun ab : Triangle N ↦ D^[ab.val.1] (H^[ab.val.2] v)) (pderiv ij P) ≠ 0) ∧
      (∀ Q : MvPolynomial (Triangle N) F,
        MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v)) Q = 0
          ↔ P ∣ Q) := by
  by_cases hN : N = 0
  · subst N
    obtain ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, hroot, hsep, hker⟩ :=
      ZeroOrderNewtonRoot.exists_differential_factor_root P hP δ η hc
    exact ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, hroot,
      ⟨leader 0, hsep⟩, hker⟩
  · obtain ⟨c, hPc, hdeg⟩ := exists_noncharacteristic_change (k := k) P hP horder
      (Nat.pos_of_ne_zero hN)
    let η₀ : Derivation k F F := η + (-c) • δ
    have hc₀ : Function.Commute δ η₀ := DirectionDerivations.commute_add_smul δ η hc (-c)
    obtain ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, hroot, hsep, hker⟩ :=
      ZeroOrderNewtonRoot.exists_differential_factor_root_all_orders
        (change (algebraMap k F c) P) hPc hdeg δ η₀ hc₀
    let H' : Derivation k E E := H + c • D
    let jets : Triangle N → E := fun ij ↦ D^[ij.val.1] (H'^[ij.val.2] v)
    have heval (Q : MvPolynomial (Triangle N) F) :
        MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v))
            (change (algebraMap k F c) Q) = MvPolynomial.aeval jets Q :=
      DirectionDerivations.aeval_change D H hDH c v Q
    refine ⟨E, hE, hKE, hFE, hKF, D, H', v,
      DirectionDerivations.commute_add_smul D H hDH c, hD, ?_, ?_, ?_, ?_⟩
    · intro a
      have he := DirectionDerivations.add_smul_restrict δ η₀ D H c hD hH a
      simpa only [η₀, DirectionDerivations.add_neg_smul_cancel] using he
    · exact (heval P).symm.trans hroot
    · by_contra hz
      push Not at hz
      apply hsep
      rw [pderiv_leader_change, heval, map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [map_mul, hz (JetLeaderDirection.topJet N j), mul_zero]
    · intro Q
      rw [← heval, hker]
      exact map_dvd_iff (changeEquiv (algebraMap k F c))

/-- Exact factorization of the leading jet polynomial produces a root and a
nonzero translated homogeneous term in the same commuting differential extension. -/
theorem exists_polynomial_step (Ψ : MvPolynomial (ℕ × ℕ) F)
    (hΨ : ¬ IsUnit Ψ) (hΨ0 : Ψ ≠ 0)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) :
    ∃ (m : ℕ), 0 < m ∧
      ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
        (_ : IsScalarTower k F E), ∃ (D H : Derivation k E E) (v : E),
        Function.Commute D H ∧
        (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
        (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
        (let jets : ℕ × ℕ → E := fun ij ↦ D^[ij.1] (H^[ij.2] v)
        let translated := NewtonTranslation.translate jets (MvPolynomial.map (algebraMap F E) Ψ)
        MvPolynomial.aeval jets Ψ = 0 ∧
        (∀ j < m, homogeneousComponent j translated = 0) ∧
        homogeneousComponent m translated ≠ 0) := by
  obtain ⟨P, Q, m, hP, hm, heq, hnd, horder⟩ :=
    exists_triangle_exact_factorization Ψ hΨ hΨ0
  obtain ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, hroot, ⟨ij, hsep⟩, hker⟩ :=
    exists_differential_factor_root P hP horder δ η hc
  let jets : ℕ × ℕ → E := fun ij ↦ D^[ij.1] (H^[ij.2] v)
  let P₀ := includeTriangle (differentialOrder Ψ) P
  let Q₀ := includeTriangle (differentialOrder Ψ) Q
  have heq' : Ψ = P₀ ^ m * Q₀ := by simpa only [map_mul, map_pow] using heq
  have hp : MvPolynomial.aeval jets P₀ = 0 := by
    rw [aeval_includeTriangle]
    exact hroot
  have hq : MvPolynomial.aeval jets Q₀ ≠ 0 := by
    rw [aeval_includeTriangle]
    exact fun hz ↦ hnd ((hker Q).mp hz)
  have hs : MvPolynomial.aeval jets (pderiv ij.val P₀) ≠ 0 := by
    dsimp [P₀, includeTriangle]
    rw [pderiv_rename Subtype.val_injective, MvPolynomial.aeval_rename]
    exact hsep
  have hev (A : MvPolynomial (ℕ × ℕ) F) :
      MvPolynomial.eval jets (MvPolynomial.map (algebraMap F E) A) =
        MvPolynomial.aeval jets A := by
    rw [MvPolynomial.eval_map]
    rfl
  have hlow := NewtonTranslation.translated_factor_lowest_term jets
    (MvPolynomial.map (algebraMap F E) P₀) (MvPolynomial.map (algebraMap F E) Q₀)
    m ij.val (by rwa [hev]) (by rwa [hev]) (by rwa [pderiv_map, hev])
  refine ⟨m, hm, E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change MvPolynomial.aeval jets Ψ = 0
    rw [heq', map_mul, map_pow, hp, zero_pow (Nat.ne_of_gt hm), zero_mul]
  · simpa only [heq', map_mul, map_pow] using hlow.1
  · simpa only [heq', map_mul, map_pow] using hlow.2.2

end
end MakarLimanov.GeneralNewtonRoot
