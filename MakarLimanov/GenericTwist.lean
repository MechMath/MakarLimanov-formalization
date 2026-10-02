import MakarLimanov.GenericJets
import MakarLimanov.JetTransform
import MakarLimanov.CentralTwist

/-!
Concrete differential extensions supporting generic elements before and after a central twist.
-/

namespace MakarLimanov.GenericTwist

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Adjoining all jets makes both `w` and `e*w` differential indeterminates over the base field. -/
theorem eigenvector_generic_extension (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (e s : F) (he : e ≠ 0) (heδ : δ e = 0) (heη : η e = s * e)
    (hsδ : δ s = 0) (hsη : η s = 0) :
    let E := FractionRing (MvPolynomial (ℕ × ℕ) F)
    ∃ (D H : Derivation k E E) (w : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      (∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0) ∧
      (∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
          D^[ij.1] (H^[ij.2] (algebraMap F E e * w))) P ≠ 0) := by
  let E := FractionRing (MvPolynomial (ℕ × ℕ) F)
  obtain ⟨D, H, w, hDH, hD, hH, hw⟩ := GenericJets.exists_generic δ η hc
  refine ⟨D, H, w, hDH, hD, hH, hw, ?_⟩
  apply JetTransform.twisted_generic D H e he s w
  · rw [hD, heδ, map_zero]
  · rw [hH, heη, map_mul]
  · rw [hD, hsδ, map_zero]
  · rw [hH, hsη, map_zero]
  · exact hw

/-- A rational eigenvalue admits a nonzero eigenvector and both compatible generic elements. -/
theorem rational_twist_generic_extension (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (q : ℤ) :
    let L := FractionRing (MvPolynomial Unit F)
    let E := FractionRing (MvPolynomial (ℕ × ℕ) L)
    ∃ (D H : Derivation k E E) (e : L) (w : E),
      e ≠ 0 ∧ Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      D (algebraMap L E e) = 0 ∧
      H (algebraMap L E e) = (p : E)⁻¹ * (q : E) * algebraMap L E e ∧
      (∀ P : MvPolynomial (ℕ × ℕ) L, P ≠ 0 →
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0) ∧
      (∀ P : MvPolynomial (ℕ × ℕ) L, P ≠ 0 →
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
          D^[ij.1] (H^[ij.2] (algebraMap L E e * w))) P ≠ 0) := by
  let L := FractionRing (MvPolynomial Unit F)
  let E := FractionRing (MvPolynomial (ℕ × ℕ) L)
  let c : F := (p : F)⁻¹ * (q : F)
  have hcδ : δ c = 0 := by simp [c, Derivation.leibniz, Derivation.leibniz_inv]
  have hcη : η c = 0 := by simp [c, Derivation.leibniz, Derivation.leibniz_inv]
  let δ₁ := CentralTwist.delta (E := L) δ
  let η₁ := CentralTwist.eta (E := L) η c
  let e : L := CentralTwist.element (F := F)
  have he : e ≠ 0 := CentralTwist.element_ne_zero
  have h₁ : Function.Commute δ₁ η₁ := CentralTwist.commute δ η hc c hcδ
  obtain ⟨D, H, w, hDH, hD, hH, hw, hew⟩ :=
    eigenvector_generic_extension δ₁ η₁ h₁ e (algebraMap F L c) he
      (CentralTwist.delta_element δ) (CentralTwist.eta_element η c)
      (by simp [δ₁, hcδ]) (by simp [η₁, hcη])
  refine ⟨D, H, e, w, he, hDH, ?_, ?_, ?_, ?_, hw, hew⟩
  · intro a
    rw [IsScalarTower.algebraMap_apply F L E, hD]
    rw [CentralTwist.delta_base]
    exact (IsScalarTower.algebraMap_apply F L E (δ a)).symm
  · intro a
    rw [IsScalarTower.algebraMap_apply F L E, hH]
    rw [CentralTwist.eta_base]
    exact (IsScalarTower.algebraMap_apply F L E (η a)).symm
  · rw [hD]
    simp [δ₁, e]
  · rw [hH]
    have heη : η₁ e = algebraMap F L c * e := CentralTwist.eta_element η c
    rw [heη, map_mul]
    congr 1
    change algebraMap L E (algebraMap F L ((p : F)⁻¹ * (q : F))) = _
    simp only [map_mul, map_inv₀, map_natCast, map_intCast]

end

end MakarLimanov.GenericTwist
