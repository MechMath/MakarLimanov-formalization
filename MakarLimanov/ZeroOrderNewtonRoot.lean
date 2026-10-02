import MakarLimanov.DifferentialNewtonStep
import MakarLimanov.CommutingDerivations

/-!
# Zero-order equations in commuting differential extensions

At differential order zero the jet triangle consists only of the unknown itself.
An irreducible equation therefore defines a separable algebraic extension. The
two derivations extend uniquely to that field and continue to commute.
-/

namespace MakarLimanov.ZeroOrderNewtonRoot

open MvPolynomial NewtonCKRoot NewtonTranslation

noncomputable section

universe u

theorem zero_jet_eq_leader (ij : Triangle 0) : ij = leader 0 := by
  apply Subtype.ext
  have h := ij.property
  apply Prod.ext <;> dsimp [leader] <;> omega

/-- The zero-order triangle has exactly one coordinate. -/
def zeroIndexEquiv : Triangle 0 ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := leader 0
  left_inv ij := (zero_jet_eq_leader ij).symm
  right_inv x := by cases x; rfl

variable {k F : Type u} [CommRing k] [Field F] [CharZero F] [Algebra k F]

/-- Encode the single zero-order jet as the variable of a univariate polynomial. -/
def zeroPolynomialEquiv : MvPolynomial (Triangle 0) F ≃ₐ[F] Polynomial F :=
  (renameEquiv F zeroIndexEquiv).trans (pUnitAlgEquiv F)

omit [CharZero F] in
@[simp] theorem zeroPolynomialEquiv_C (a : F) :
    zeroPolynomialEquiv (C a) = Polynomial.C a := by
  simp [zeroPolynomialEquiv]

omit [CharZero F] in
@[simp] theorem zeroPolynomialEquiv_X (ij : Triangle 0) :
    zeroPolynomialEquiv (X ij : MvPolynomial (Triangle 0) F) = Polynomial.X := by
  simp [zeroPolynomialEquiv]

omit [CharZero F] in
theorem zeroPolynomialEquiv_pderiv (P : MvPolynomial (Triangle 0) F) :
    zeroPolynomialEquiv (pderiv (leader 0) P) =
      (zeroPolynomialEquiv P).derivative := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P ij hP =>
    rw [zero_jet_eq_leader ij]
    simp [Derivation.leibniz, smul_eq_mul, hP, Polynomial.derivative_mul, mul_comm]

omit [CharZero F] in
theorem aeval_zeroPolynomialEquiv {E : Type*} [CommRing E] [Algebra F E]
    (v : E) (P : MvPolynomial (Triangle 0) F) :
    Polynomial.aeval v (zeroPolynomialEquiv P) = MvPolynomial.aeval (fun _ ↦ v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P ij hP => simp [hP]

/-- An irreducible zero-order jet equation has a root in a compatible commuting extension. -/
theorem exists_differential_factor_root (P : MvPolynomial (Triangle 0) F)
    (hP : Irreducible P) (δ η : Derivation k F F) (hc : Function.Commute δ η) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E), ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      MvPolynomial.aeval (fun ij : Triangle 0 ↦ D^[ij.val.1] (H^[ij.val.2] v)) P = 0 ∧
      MvPolynomial.aeval (fun ij : Triangle 0 ↦ D^[ij.val.1] (H^[ij.val.2] v))
          (pderiv (leader 0) P) ≠ 0 ∧
      (∀ Q : MvPolynomial (Triangle 0) F,
        MvPolynomial.aeval (fun ij : Triangle 0 ↦ D^[ij.val.1] (H^[ij.val.2] v)) Q = 0
          ↔ P ∣ Q) := by
  let p := zeroPolynomialEquiv P
  letI : Fact (Irreducible p) := ⟨hP.map zeroPolynomialEquiv⟩
  let E := AdjoinRoot p
  have : Algebra.IsSeparable F E := AlgebraicBranch.separable p
  let ds : CommutingDerivations k F := ⟨δ, η, hc⟩
  let D := ds.extendDelta E
  let H := ds.extendEta E
  let v : E := AdjoinRoot.root p
  have hjets : (fun ij : Triangle 0 ↦ D^[ij.val.1] (H^[ij.val.2] v)) = fun _ ↦ v := by
    funext ij
    rw [zero_jet_eq_leader ij]
    rfl
  have hvalue (Q : MvPolynomial (Triangle 0) F) :
      MvPolynomial.aeval (fun ij : Triangle 0 ↦ D^[ij.val.1] (H^[ij.val.2] v)) Q =
        Polynomial.aeval v (zeroPolynomialEquiv Q) := by
    rw [hjets, aeval_zeroPolynomialEquiv]
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    D, H, v, ds.extensions_commute E, ds.extendDelta_apply E, ds.extendEta_apply E,
    ?_, ?_, ?_⟩
  · rw [hvalue]
    exact AlgebraicBranch.root_equation p
  · rw [hvalue, zeroPolynomialEquiv_pderiv]
    exact AlgebraicBranch.separant_nonzero p
  · intro Q
    rw [hvalue, AlgebraicBranch.kernel_iff]
    exact map_dvd_iff zeroPolynomialEquiv

/-- The algebraic and positive-order branches give one root theorem at every jet order. -/
theorem exists_differential_factor_root_all_orders {N : ℕ}
    (P : MvPolynomial (Triangle N) F) (hP : Irreducible P)
    (hdeg : (stripPolynomial P).natDegree ≠ 0)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E), ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v)) P = 0 ∧
      MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v))
          (pderiv (leader N) P) ≠ 0 ∧
      (∀ Q : MvPolynomial (Triangle N) F,
        MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v)) Q = 0
          ↔ P ∣ Q) := by
  by_cases hN : N = 0
  · subst N
    exact exists_differential_factor_root P hP δ η hc
  · exact NewtonCKRoot.exists_differential_factor_root P hP hdeg δ η hc (Nat.pos_of_ne_zero hN)

/-- A zero-order factor gives the same nonzero translated lowest term as a differential factor. -/
theorem exists_step (P Q : MvPolynomial (Triangle 0) F)
    (hP : Irreducible P) (hQ : ¬ P ∣ Q)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) (m : ℕ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E),
      ∃ (D H : Derivation k E E) (v : E),
        Function.Commute D H ∧
        (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
        (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
        (let jets : Triangle 0 → E := fun ij ↦ D^[ij.val.1] (H^[ij.val.2] v)
        let translated := translate jets (MvPolynomial.map (algebraMap F E) (P ^ m * Q))
        MvPolynomial.aeval jets P = 0 ∧
        MvPolynomial.aeval jets Q ≠ 0 ∧
        MvPolynomial.aeval jets (pderiv (leader 0) P) ≠ 0 ∧
        (∀ j < m, homogeneousComponent j translated = 0) ∧
        homogeneousComponent m translated =
          C (MvPolynomial.aeval jets Q) *
            linearization jets (MvPolynomial.map (algebraMap F E) P) ^ m ∧
        homogeneousComponent m translated ≠ 0) := by
  obtain ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, hroot, hsep, hker⟩ :=
    exists_differential_factor_root P hP δ η hc
  let jets : Triangle 0 → E := fun ij ↦ D^[ij.val.1] (H^[ij.val.2] v)
  have hQv : MvPolynomial.aeval jets Q ≠ 0 := fun hz ↦ hQ ((hker Q).mp hz)
  have hmap (A : MvPolynomial (Triangle 0) F) :
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
      (pderiv (leader 0) (MvPolynomial.map (algebraMap F E) P)) ≠ 0 := by
    rw [MvPolynomial.pderiv_map, hmap]
    exact hsep
  have hlowest := translated_factor_lowest_term jets
    (MvPolynomial.map (algebraMap F E) P) (MvPolynomial.map (algebraMap F E) Q)
    m (leader 0) hroot' hQv' hsep'
  refine ⟨E, hE, hKE, hFE, hKF, D, H, v, hDH, hD, hH, ?_⟩
  refine ⟨hroot, hQv, hsep, ?_⟩
  simpa only [map_mul, map_pow, hmap] using hlowest

/-- Newton factor translation is available uniformly, including order zero. -/
theorem exists_step_all_orders {N : ℕ} (P Q : MvPolynomial (Triangle N) F)
    (hP : Irreducible P) (hdeg : (stripPolynomial P).natDegree ≠ 0)
    (hQ : ¬ P ∣ Q) (δ η : Derivation k F F) (hc : Function.Commute δ η) (m : ℕ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E),
      ∃ (D H : Derivation k E E) (v : E),
        Function.Commute D H ∧
        (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
        (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
        (let jets : Triangle N → E := fun ij ↦ D^[ij.val.1] (H^[ij.val.2] v)
        let translated := translate jets (MvPolynomial.map (algebraMap F E) (P ^ m * Q))
        MvPolynomial.aeval jets P = 0 ∧
        MvPolynomial.aeval jets Q ≠ 0 ∧
        MvPolynomial.aeval jets (pderiv (leader N) P) ≠ 0 ∧
        (∀ j < m, homogeneousComponent j translated = 0) ∧
        homogeneousComponent m translated =
          C (MvPolynomial.aeval jets Q) *
            linearization jets (MvPolynomial.map (algebraMap F E) P) ^ m ∧
        homogeneousComponent m translated ≠ 0) := by
  by_cases hN : N = 0
  · subst N
    exact exists_step P Q hP hQ δ η hc m
  · exact DifferentialNewtonStep.exists_step P Q hP hdeg hQ δ η hc (Nat.pos_of_ne_zero hN) m

end

end MakarLimanov.ZeroOrderNewtonRoot
