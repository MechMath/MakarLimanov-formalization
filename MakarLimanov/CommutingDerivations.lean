import MakarLimanov.DifferentialExtension

/-! Two explicit commuting derivations and their compatible separable extensions. -/

namespace MakarLimanov

variable (k F : Type*) [CommRing k] [Field F] [Algebra k F]

/-- Differential data with two derivations fixing the specified base ring. -/
structure CommutingDerivations where
  delta : Derivation k F F
  eta : Derivation k F F
  commute : Function.Commute delta eta

namespace CommutingDerivations

variable {k F} (ds : CommutingDerivations k F)
variable (E : Type*) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra.IsSeparable F E]

/-- Extension of the first derivation to a separable field extension. -/
noncomputable def extendDelta : Derivation k E E :=
  DifferentialExtension.extendDerivation (K := F)
    ((Algebra.linearMap F E).compDer ds.delta)

/-- Extension of the second derivation to a separable field extension. -/
noncomputable def extendEta : Derivation k E E :=
  DifferentialExtension.extendDerivation (K := F)
    ((Algebra.linearMap F E).compDer ds.eta)

@[simp]
theorem extendDelta_apply (x : F) :
    ds.extendDelta E (algebraMap F E x) = algebraMap F E (ds.delta x) := by
  simp [extendDelta, DifferentialExtension.extendDerivation_apply, LinearMap.compDer]

@[simp]
theorem extendEta_apply (x : F) :
    ds.extendEta E (algebraMap F E x) = algebraMap F E (ds.eta x) := by
  simp [extendEta, DifferentialExtension.extendDerivation_apply, LinearMap.compDer]

theorem extensions_commute : Function.Commute (ds.extendDelta E) (ds.extendEta E) := by
  apply DifferentialExtension.commute_of_commute_on_base (K := F)
  intro x
  simp only [extendEta_apply, extendDelta_apply, ds.commute x]

/-- A separable extension inherits compatible commuting differential data. -/
noncomputable def extend : CommutingDerivations k E where
  delta := ds.extendDelta E
  eta := ds.extendEta E
  commute := ds.extensions_commute E

end CommutingDerivations
end MakarLimanov
