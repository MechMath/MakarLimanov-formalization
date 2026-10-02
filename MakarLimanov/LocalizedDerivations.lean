import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.FractionRing

/-! Derivation constructors used by the differential-field branch. -/

namespace MakarLimanov.LocalizedDerivations

open TensorProduct
variable {k R S E : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing E]
  [Algebra k R] [Algebra k S] [Algebra k E] [Algebra R S] [Algebra R E] [Algebra S E]
  [IsScalarTower k R S] [IsScalarTower k R E] [IsScalarTower k S E] [IsScalarTower R S E]
noncomputable def extendEtaleDerivation [Algebra.FormallyEtale R S]
    (d : Derivation k R E) : Derivation k S E :=
  ((d.liftKaehlerDifferential.liftBaseChange S).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S).symm.toLinearMap).compDer
      (KaehlerDifferential.D k S)
lemma extendEtaleDerivation_apply [Algebra.FormallyEtale R S]
    (d : Derivation k R E) (x : R) :
    extendEtaleDerivation (S := S) d (algebraMap R S x) = d x := by
  simp [extendEtaleDerivation, LinearMap.compDer,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
noncomputable def extendLocalizedDerivation (M : Submonoid R) [IsLocalization M S]
    (d : Derivation k R E) : Derivation k S E := by
  letI : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  exact extendEtaleDerivation d
lemma extendLocalizedDerivation_apply (M : Submonoid R) [IsLocalization M S]
    (d : Derivation k R E) (x : R) :
    extendLocalizedDerivation (S := S) M d (algebraMap R S x) = d x := by
  letI : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  exact extendEtaleDerivation_apply d x

end MakarLimanov.LocalizedDerivations
