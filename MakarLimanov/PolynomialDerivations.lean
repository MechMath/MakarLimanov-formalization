import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! Derivation constructors used by the differential-field branch. -/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.PolynomialDerivations

open TrivSqZeroExt
variable {k F E : Type*} [CommRing k] [CommRing F] [CommRing E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
def derivationDual (d : Derivation k F E) : F →ₐ[k] TrivSqZeroExt E E where
  toFun a := ⟨algebraMap F E a, d a⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp [fst_add, snd_add]
  map_mul' a b := by ext <;> simp [fst_mul, snd_mul, Derivation.leibniz, Algebra.smul_def, mul_comm]
  commutes' a := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', IsScalarTower.algebraMap_apply k F E]
def derivationFromDual (f : F →ₐ[k] TrivSqZeroExt E E)
    (hf : ∀ a, (f a).fst = algebraMap F E a) : Derivation k F E where
  toFun a := (f a).snd
  map_add' a b := by simp
  map_smul' a b := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by simp [hf, Algebra.smul_def, mul_comm]
variable {σ : Type*} [Algebra (MvPolynomial σ F) E]
  [IsScalarTower F (MvPolynomial σ F) E]
  [IsScalarTower k (MvPolynomial σ F) E]
noncomputable def mvDerivationDual (d : Derivation k F E) (dx : σ → E) :
    MvPolynomial σ F →ₐ[k] TrivSqZeroExt E E :=
  MvPolynomial.aevalTower (derivationDual d)
    (fun i ↦ ⟨algebraMap (MvPolynomial σ F) E (MvPolynomial.X i), dx i⟩)
lemma mvDerivationDual_fst (d : Derivation k F E) (dx : σ → E)
    (p : MvPolynomial σ F) :
    (mvDerivationDual d dx p).fst = algebraMap (MvPolynomial σ F) E p := by
  have h : (TrivSqZeroExt.fstHom k E E).comp (mvDerivationDual d dx) =
      IsScalarTower.toAlgHom k (MvPolynomial σ F) E := by
    apply AlgHom.coe_ringHom_injective
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.aevalTower_C, MvPolynomial.aevalTower_X, mvDerivationDual, derivationDual, IsScalarTower.algebraMap_apply F (MvPolynomial σ F) E]
    · intro i
      simp [MvPolynomial.aevalTower_C, MvPolynomial.aevalTower_X, mvDerivationDual]
  exact DFunLike.congr_fun h p
noncomputable def mvDerivation (d : Derivation k F E) (dx : σ → E) :
    Derivation k (MvPolynomial σ F) E :=
  derivationFromDual (mvDerivationDual d dx) (mvDerivationDual_fst d dx)
lemma mvDerivation_C (d : Derivation k F E) (dx : σ → E) (a : F) :
    mvDerivation d dx (MvPolynomial.C a) = d a := by
  simp [MvPolynomial.aevalTower_C, MvPolynomial.aevalTower_X, mvDerivation, derivationFromDual, mvDerivationDual, derivationDual]
lemma mvDerivation_X (d : Derivation k F E) (dx : σ → E) (i : σ) :
    mvDerivation d dx (MvPolynomial.X i) = dx i := by
  simp [MvPolynomial.aevalTower_C, MvPolynomial.aevalTower_X, mvDerivation, derivationFromDual, mvDerivationDual]
omit [Algebra (MvPolynomial σ F) E] [IsScalarTower F (MvPolynomial σ F) E]
  [IsScalarTower k (MvPolynomial σ F) E] in
noncomputable def mvEvalDerivation (d : Derivation k F E) (x dx : σ → E) :
    letI : Algebra (MvPolynomial σ F) E := (MvPolynomial.aeval x).toRingHom.toAlgebra
    Derivation k (MvPolynomial σ F) E := by
  letI : Algebra (MvPolynomial σ F) E := (MvPolynomial.aeval x).toRingHom.toAlgebra
  haveI : IsScalarTower F (MvPolynomial σ F) E :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower k (MvPolynomial σ F) E :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      simp [IsScalarTower.algebraMap_apply k F (MvPolynomial σ F),
        RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply k F E]
  exact mvDerivation d dx

end MakarLimanov.PolynomialDerivations
