import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Derivation.Lie
/-! General separable-field derivation extension via Kähler differentials. -/

namespace MakarLimanov.DifferentialExtension

open TensorProduct
variable {k K E : Type*} [CommRing k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
  [Algebra.IsSeparable K E]
noncomputable def extendDerivation (d : Derivation k K E) : Derivation k E E := by
  letI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  exact ((d.liftKaehlerDifferential.liftBaseChange E).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k K E).symm.toLinearMap).compDer
      (KaehlerDifferential.D k E)
lemma extendDerivation_apply (d : Derivation k K E) (x : K) :
    extendDerivation d (algebraMap K E x) = d x := by
  letI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  simp [extendDerivation, LinearMap.compDer,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
omit [Algebra k K] [IsScalarTower k K E] in
lemma derivation_eq_zero_of_restrict_eq_zero (d : Derivation k E E)
    (hd : ∀ x : K, d (algebraMap K E x) = 0) : d = 0 := by
  letI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let dK : Derivation K E E :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun a x ↦ by
        simp [Algebra.smul_def, Derivation.leibniz, hd]
      map_one_eq_zero' := d.map_one_eq_zero
      leibniz' := d.leibniz }
  have hz : dK.liftKaehlerDifferential = 0 := Subsingleton.elim _ _
  ext x
  have hx := congrArg (fun f : KaehlerDifferential K E →ₗ[E] E ↦
    f (KaehlerDifferential.D K E x)) hz
  simpa using hx
omit [Algebra k K] [IsScalarTower k K E] in
lemma derivation_ext_of_separable (d₁ d₂ : Derivation k E E)
    (h : ∀ x : K, d₁ (algebraMap K E x) = d₂ (algebraMap K E x)) : d₁ = d₂ := by
  apply sub_eq_zero.mp
  apply derivation_eq_zero_of_restrict_eq_zero (K := K)
  intro x
  simp [h]
omit [Algebra k K] [IsScalarTower k K E] in
lemma commute_of_commute_on_base (d h : Derivation k E E)
    (hc : ∀ x : K, d (h (algebraMap K E x)) = h (d (algebraMap K E x))) :
    Function.Commute d h := by
  have hz : ⁅d, h⁆ = 0 := derivation_eq_zero_of_restrict_eq_zero (K := K) ⁅d, h⁆
    (fun x ↦ by simp [Derivation.commutator_apply, hc])
  intro x
  have hx := DFunLike.congr_fun hz x
  simpa [Derivation.commutator_apply, sub_eq_zero] using hx
lemma existsUnique_derivation_extension (d : Derivation k K E) :
    ∃! D : Derivation k E E, ∀ x : K, D (algebraMap K E x) = d x := by
  refine ⟨extendDerivation d, extendDerivation_apply d, ?_⟩
  intro D hD
  exact derivation_ext_of_separable (K := K) D (extendDerivation d)
    (fun x ↦ (hD x).trans (extendDerivation_apply d x).symm)

end MakarLimanov.DifferentialExtension
