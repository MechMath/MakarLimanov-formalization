import MakarLimanov.CKStrip
import MakarLimanov.SymbolSeries

/-! A concrete rational differential extension supplying the central monomial twist. -/

namespace MakarLimanov.CentralTwist

open CKStrip

noncomputable section

variable {k F E : Type*} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial Unit F) E]
  [IsScalarTower F (MvPolynomial Unit F) E]
  [IsScalarTower k (MvPolynomial Unit F) E]
  [IsFractionRing (MvPolynomial Unit F) E]

/-- The transcendental element adjoined to the coefficient field. -/
def element : E := algebraMap (MvPolynomial Unit F) E (MvPolynomial.X ())

omit [Algebra F E] [IsScalarTower F (MvPolynomial Unit F) E] in
lemma element_ne_zero : element (F := F) (E := E) ≠ 0 := by
  simpa only [element, map_zero] using
    (IsFractionRing.injective (MvPolynomial Unit F) E).ne (MvPolynomial.X_ne_zero ())

/-- Extend the first derivation by killing the new transcendental element. -/
def delta (δ : Derivation k F F) : Derivation k E E :=
  rationalDerivation ((Algebra.linearMap F E).compDer δ) (fun _ : Unit ↦ 0)

/-- Extend the second derivation by prescribing the eigenvalue of the new element. -/
def eta (η : Derivation k F F) (c : F) : Derivation k E E :=
  rationalDerivation ((Algebra.linearMap F E).compDer η)
    (fun _ : Unit ↦ algebraMap F E c * element (F := F))

@[simp] lemma delta_base (δ : Derivation k F F) (a : F) :
    delta (E := E) δ (algebraMap F E a) = algebraMap F E (δ a) := by
  simp [delta, rationalDerivation_C, LinearMap.compDer]

@[simp] lemma eta_base (η : Derivation k F F) (c a : F) :
    eta (E := E) η c (algebraMap F E a) = algebraMap F E (η a) := by
  simp [eta, rationalDerivation_C, LinearMap.compDer]

@[simp] lemma delta_element (δ : Derivation k F F) :
    delta (E := E) δ (element (F := F)) = 0 := by
  simp [delta, element, rationalDerivation_X]

@[simp] lemma eta_element (η : Derivation k F F) (c : F) :
    eta (E := E) η c (element (F := F)) = algebraMap F E c * element (F := F) := by
  simp [eta, element, rationalDerivation_X]

/-- Commutation on the original field and the new generator determines commutation everywhere. -/
theorem commute (δ η₀ : Derivation k F F) (h : Function.Commute δ η₀)
    (c : F) (hc : δ c = 0) :
    Function.Commute (delta (E := E) δ) (eta (E := E) η₀ c) := by
  have hz : ⁅delta (E := E) δ, eta (E := E) η₀ c⁆ = 0 := by
    apply derivation_ext_rational (F := F) (σ := Unit)
    · intro a
      simp [Derivation.commutator_apply, h a]
    · intro i
      cases i
      change delta (E := E) δ (eta (E := E) η₀ c (element (F := F))) -
        eta (E := E) η₀ c (delta (E := E) δ (element (F := F))) = (0 : E)
      simp [Derivation.leibniz, hc]
  intro a
  have ha := DFunLike.congr_fun hz a
  simpa [Derivation.commutator_apply, sub_eq_zero] using ha

/-- A concrete fraction field contains a nonzero eigenvector for compatible extended derivations. -/
theorem exists_extension (δ η₀ : Derivation k F F) (h : Function.Commute δ η₀)
    (c : F) (hc : δ c = 0) :
    ∃ (D H : Derivation k (FractionRing (MvPolynomial Unit F))
        (FractionRing (MvPolynomial Unit F))) (e : FractionRing (MvPolynomial Unit F)),
      e ≠ 0 ∧ Function.Commute D H ∧
      (∀ a : F, D (algebraMap F _ a) = algebraMap F _ (δ a)) ∧
      (∀ a : F, H (algebraMap F _ a) = algebraMap F _ (η₀ a)) ∧
      D e = 0 ∧ H e = algebraMap F _ c * e := by
  exact ⟨delta δ, eta η₀ c, element, element_ne_zero, commute δ η₀ h c hc,
    delta_base δ, eta_base η₀ c, delta_element δ, eta_element η₀ c⟩

/-- The prescribed rational eigenvalue produces an actual central invertible symbol. -/
theorem twist_properties (δ η₀ : Derivation k F F) (h : Function.Commute δ η₀)
    (p : ℕ) (hp : 0 < p) (n : ℤ) :
    let c : F := (p : F)⁻¹ * (n : F)
    let D := delta (E := E) δ
    let H := eta (E := E) η₀ c
    let z : LaurentSeries E := HahnSeries.single n (element (F := F) (E := E))
    Function.Commute D H ∧ z ≠ 0 ∧
      (∀ x, SymbolSeries.starProduct p hp D H z x = z * x ∧
        SymbolSeries.starProduct p hp D H x z = z * x) ∧
      SymbolSeries.starProduct p hp D H z z⁻¹ = 1 ∧
      SymbolSeries.starProduct p hp D H z⁻¹ z = 1 := by
  dsimp only
  have hc : δ ((p : F)⁻¹ * (n : F)) = 0 := by
    simp [Derivation.leibniz, Derivation.leibniz_inv]
  have hz : (HahnSeries.single n (element (F := F) (E := E)) : LaurentSeries E) ≠ 0 := by
    intro hz
    have he := congrArg (fun x : LaurentSeries E ↦ x.coeff n) hz
    exact element_ne_zero (by simpa using he)
  have hk := SymbolSeries.monomial_twist_killed p (delta (E := E) δ)
    (eta (E := E) η₀ ((p : F)⁻¹ * (n : F))) n (element (F := F) (E := E))
    (delta_element δ) (by simp [eta_element, mul_assoc])
  refine ⟨commute δ η₀ h _ hc, hz, ?_, ?_⟩
  · intro x
    exact SymbolSeries.starProduct_central p hp _ _ _ x hk.1 hk.2
  · exact SymbolSeries.starProduct_central_inverse p hp _ _ _ hz hk.1 hk.2

end
end MakarLimanov.CentralTwist
