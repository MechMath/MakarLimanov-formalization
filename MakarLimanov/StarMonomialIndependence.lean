import MakarLimanov.ConcreteStarMonomials
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Independence of the concrete Laurent monomials

The Laurent exponent together with the two polynomial exponents recover
`(l,Q,d)`.  Algebraic independence of the rational coefficient variables and
coefficient extraction therefore make their finite linear combinations
unique.
-/

noncomputable section

namespace MakarLimanov.StarMonomialIndependence

open HahnSeries TwoVariableDifferentialField ConcreteStarMonomials

variable {C : Type*} [Field C]

private def exponents (l Q : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 l + Finsupp.single 1 Q

private theorem coefficient_eq_monomial (l Q : ℕ) :
    coefficient (C := C) l Q =
      algebraMap (MvPolynomial (Fin 2) C) (RationalField C)
        (MvPolynomial.monomial (exponents l Q) 1) := by
  simp only [coefficient, tau, upsilon, ← map_pow, ← map_mul,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
  rfl

private def encoding (t : ℕ × ℕ × ℕ) : Σ _ : ℤ, Fin 2 →₀ ℕ :=
  ⟨(t.2.1 : ℤ) - (t.2.2 : ℤ), exponents t.1 t.2.1⟩

private theorem encoding_injective : Function.Injective encoding := by
  rintro ⟨l, Q, d⟩ ⟨l', Q', d'⟩ h
  have hn : (Q : ℤ) - d = (Q' : ℤ) - d' := congrArg Sigma.fst h
  have hm : exponents l Q = exponents l' Q' :=
    congrArg (fun t : Σ _ : ℤ, Fin 2 →₀ ℕ ↦ t.2) h
  have hl : l = l' := by
    simpa [exponents] using congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) hm
  have hQ : Q = Q' := by
    simpa [exponents] using congrArg (fun m : Fin 2 →₀ ℕ ↦ m 1) hm
  have hd : d = d' := by omega
  simp [hl, hQ, hd]

/-- The concrete monomials are linearly independent over the constant field. -/
theorem monomial_linearIndependent :
    LinearIndependent C (fun t : ℕ × ℕ × ℕ ↦
      monomial (C := C) t.1 t.2.1 t.2.2) := by
  classical
  let φ : MvPolynomial (Fin 2) C →ₗ[C] RationalField C :=
    (IsScalarTower.toAlgHom C (MvPolynomial (Fin 2) C) (RationalField C)).toLinearMap
  have hφ : Function.Injective φ :=
    IsFractionRing.injective (MvPolynomial (Fin 2) C) (RationalField C)
  have hpoly : LinearIndependent C (fun m : Fin 2 →₀ ℕ ↦
      algebraMap (MvPolynomial (Fin 2) C) (RationalField C)
        (MvPolynomial.monomial m 1)) := by
    exact (MvPolynomial.basisMonomials (Fin 2) C).linearIndependent.map'
      φ (LinearMap.ker_eq_bot.mpr hφ)
  have hPi := Pi.linearIndependent_single
    (R := C) (fun (_ : ℤ) (m : Fin 2 →₀ ℕ) ↦
      algebraMap (MvPolynomial (Fin 2) C) (RationalField C)
        (MvPolynomial.monomial m 1)) (fun _ ↦ hpoly)
  let coeffMap : LaurentSeries (RationalField C) →ₗ[C]
      (ℤ → RationalField C) :=
    LinearMap.pi (fun n ↦ HahnSeries.coeff.linearMap (R := C) n)
  apply LinearIndependent.of_comp coeffMap
  convert hPi.comp encoding encoding_injective using 1
  funext t n
  change (monomial (C := C) t.1 t.2.1 t.2.2).coeff n = _
  simp [monomial, coefficient_eq_monomial, encoding, HahnSeries.coeff_single,
    Pi.single_apply]

/-- A finitely supported constant-coefficient combination of the monomials. -/
def symbolLinearMap : ((ℕ × ℕ × ℕ) →₀ C) →ₗ[C]
    LaurentSeries (RationalField C) :=
  Finsupp.linearCombination C
    (fun t ↦ monomial (C := C) t.1 t.2.1 t.2.2)

@[simp] theorem symbolLinearMap_apply (v : (ℕ × ℕ × ℕ) →₀ C) :
    symbolLinearMap (C := C) v =
      v.sum (fun t c ↦ c • monomial (C := C) t.1 t.2.1 t.2.2) := rfl

@[simp] theorem symbolLinearMap_single (t : ℕ × ℕ × ℕ) (c : C) :
    symbolLinearMap (C := C) (Finsupp.single t c) =
      c • monomial (C := C) t.1 t.2.1 t.2.2 := by
  simp [symbolLinearMap]

/-- A concrete Laurent symbol uniquely determines the finite coefficient data. -/
theorem symbolLinearMap_injective : Function.Injective (symbolLinearMap (C := C)) :=
  monomial_linearIndependent

end MakarLimanov.StarMonomialIndependence

end
