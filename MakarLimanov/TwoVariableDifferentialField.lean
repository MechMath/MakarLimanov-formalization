import MakarLimanov.CKStrip

/-!
# The rational coefficient field with a partial and an Euler derivation

The variables `tau` and `upsilon` are algebraically independent. The two
derivations act by `∂tau` and `upsilon ∂upsilon` and kill the coefficient field.
-/

noncomputable section

namespace MakarLimanov.TwoVariableDifferentialField

open MvPolynomial CKStrip

variable (k C : Type*) [Field k] [Field C] [Algebra k C]

abbrev RationalField := FractionRing (MvPolynomial (Fin 2) C)

variable {k C}

/-- The first rational variable. -/
def tau : RationalField C := algebraMap (MvPolynomial (Fin 2) C) _ (X 0)

/-- The second rational variable. -/
def upsilon : RationalField C := algebraMap (MvPolynomial (Fin 2) C) _ (X 1)

/-- Partial differentiation in the first variable. -/
def delta : Derivation k (RationalField C) (RationalField C) :=
  rationalDerivation (0 : Derivation k C (RationalField C))
    (fun i : Fin 2 ↦ if i = 0 then 1 else 0)

/-- Euler differentiation in the second variable. -/
def eta : Derivation k (RationalField C) (RationalField C) :=
  rationalDerivation (0 : Derivation k C (RationalField C))
    (fun i : Fin 2 ↦ if i = 1 then upsilon else 0)

@[simp] theorem delta_base (c : C) : delta (k := k) (C := C) (algebraMap C _ c) = 0 := by
  simp [delta, rationalDerivation_C]

@[simp] theorem eta_base (c : C) : eta (k := k) (C := C) (algebraMap C _ c) = 0 := by
  simp [eta, rationalDerivation_C]

@[simp] theorem delta_tau : delta (k := k) (C := C) tau = 1 := by
  simp [delta, tau, rationalDerivation_X]

@[simp] theorem delta_upsilon : delta (k := k) (C := C) upsilon = 0 := by
  simp [delta, upsilon, rationalDerivation_X]

@[simp] theorem eta_tau : eta (k := k) (C := C) tau = 0 := by
  simp [eta, tau, rationalDerivation_X]

@[simp] theorem eta_upsilon : eta (k := k) (C := C) upsilon = upsilon := by
  simp [eta, upsilon, rationalDerivation_X]

/-- The two prescribed derivations commute on the whole rational field. -/
theorem commute : Function.Commute (delta (k := k) (C := C)) (eta (k := k) (C := C)) := by
  have hzero : ⁅delta (k := k) (C := C), eta (k := k) (C := C)⁆ = 0 := by
    apply derivation_ext_rational
      (F := C) (σ := Fin 2) (K := RationalField C)
    · intro c
      simp [Derivation.commutator_apply]
    · intro i
      fin_cases i
      · change ⁅delta (k := k) (C := C), eta (k := k) (C := C)⁆ tau = 0
        simp [Derivation.commutator_apply]
      · change ⁅delta (k := k) (C := C), eta (k := k) (C := C)⁆ upsilon = 0
        simp [Derivation.commutator_apply]
  intro a
  have ha := DFunLike.congr_fun hzero a
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using ha

end MakarLimanov.TwoVariableDifferentialField
