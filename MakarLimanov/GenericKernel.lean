import MakarLimanov.AlgebraicBranch
import MakarLimanov.CKStrip
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Generic root kernels over fraction fields

Gauss's lemma contracts divisibility by a primitive polynomial from a fraction field.
Consequently an irreducible positive-degree polynomial has a generic algebraic root whose
evaluation kernel on the original polynomial ring is exactly its principal ideal.
-/

namespace MakarLimanov.GenericKernel

open Polynomial

universe u v

variable {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
  [IsGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Divisibility by a primitive polynomial contracts from a fraction field for arbitrary Q. -/
theorem fraction_dvd_iff {P Q : R[X]} (hP : P.IsPrimitive) :
    P.map (algebraMap R K) ∣ Q.map (algebraMap R K) ↔ P ∣ Q := by
  constructor
  · rintro ⟨g, hg⟩
    have hlift : g ∈ Polynomial.lifts (algebraMap R K) := by
      apply hP.map_mul_mem_lifts_iff.mp
      rw [← hg]
      exact ⟨Q, rfl⟩
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts g).mp hlift
    refine ⟨q, ?_⟩
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [Polynomial.map_mul, hq]
    exact hg
  · rintro ⟨q, rfl⟩
    exact ⟨q.map (algebraMap R K), Polynomial.map_mul _⟩

/-- Positive degree is essential: constant irreducibles need not remain irreducible over K. -/
theorem irreducible_fraction_map {P : R[X]} (hP : Irreducible P)
    (hdeg : P.natDegree ≠ 0) : Irreducible (P.map (algebraMap R K)) :=
  (hP.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map.mp hP

/-- The concrete root quotient is a field; its ring operations are those of AdjoinRoot. -/
noncomputable abbrev genericRootField (P : R[X]) (hP : Irreducible P) (hdeg : P.natDegree ≠ 0) :
    Field (AdjoinRoot (P.map (algebraMap R K))) := by
  letI : Fact (Irreducible (P.map (algebraMap R K))) := ⟨irreducible_fraction_map hP hdeg⟩
  infer_instance

/-- The generic root has exactly the original principal ideal as evaluation kernel. -/
theorem generic_root_kernel (P : R[X]) (hP : Irreducible P) (hdeg : P.natDegree ≠ 0)
    [Fact (Irreducible (P.map (algebraMap R K)))] (Q : R[X]) :
    aeval (AdjoinRoot.root (P.map (algebraMap R K))) (Q.map (algebraMap R K)) = 0 ↔
      P ∣ Q := by
  rw [AlgebraicBranch.kernel_iff, fraction_dvd_iff (hP.isPrimitive hdeg)]

/-- A single generic algebraic root preserves every inequation not divisible by P. -/
theorem exists_generic_root [CharZero K] (P : R[X]) (hP : Irreducible P)
    (hdeg : P.natDegree ≠ 0) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra K E),
      Algebra.IsSeparable K E ∧ ∃ z : E,
        aeval z (P.map (algebraMap R K)) = 0 ∧
        (∀ Q : R[X], aeval z (Q.map (algebraMap R K)) = 0 ↔ P ∣ Q) ∧
        (∀ Q : R[X], ¬ P ∣ Q → aeval z (Q.map (algebraMap R K)) ≠ 0) ∧
        aeval z (P.derivative.map (algebraMap R K)) ≠ 0 := by
  let p := P.map (algebraMap R K)
  have hp : Irreducible p := irreducible_fraction_map hP hdeg
  letI : Fact (Irreducible p) := ⟨hp⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AlgebraicBranch.separable p,
    AdjoinRoot.root p, AlgebraicBranch.root_equation p, ?_, ?_, ?_⟩
  · intro Q
    rw [AlgebraicBranch.kernel_iff]
    exact fraction_dvd_iff (hP.isPrimitive hdeg)
  · intro Q hQ hz
    exact hQ ((fraction_dvd_iff (hP.isPrimitive hdeg)).mp
      ((AlgebraicBranch.kernel_iff p _).mp hz))
  · simpa only [p, Polynomial.derivative_map] using AlgebraicBranch.separant_nonzero p

/-- Specialization to polynomial coefficient rings, including infinitely many strip variables. -/
theorem exists_mv_generic_root {F : Type u} [Field F] [CharZero F] {σ : Type u}
    (P : Polynomial (MvPolynomial σ F)) (hP : Irreducible P) (hdeg : P.natDegree ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra (FractionRing (MvPolynomial σ F)) E),
      Algebra.IsSeparable (FractionRing (MvPolynomial σ F)) E ∧ ∃ z : E,
        aeval z (P.map (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))) = 0 ∧
        (∀ Q : Polynomial (MvPolynomial σ F),
          aeval z (Q.map (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))) = 0
            ↔ P ∣ Q) ∧
        (∀ Q : Polynomial (MvPolynomial σ F), ¬ P ∣ Q →
          aeval z (Q.map (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))) ≠ 0) ∧
        aeval z (P.derivative.map
          (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))) ≠ 0 := by
  have : CharZero (MvPolynomial σ F) :=
    charZero_of_injective_ringHom (MvPolynomial.C_injective σ F)
  have : CharZero (FractionRing (MvPolynomial σ F)) :=
    IsFractionRing.charZero_of_isFractionRing (MvPolynomial σ F)
  exact exists_generic_root P hP hdeg

section Rename

variable {A σ τ : Type*} [CommRing A]

/-- Adding algebraically independent variables does not create polynomial divisibility. -/
theorem rename_dvd_iff (f : σ → τ) (hf : Function.Injective f)
    (P Q : MvPolynomial σ A) : MvPolynomial.rename f P ∣ MvPolynomial.rename f Q ↔ P ∣ Q := by
  constructor
  · intro h
    have hm := map_dvd (MvPolynomial.killCompl hf).toRingHom h
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.killCompl_rename_app] using hm
  · exact map_dvd (MvPolynomial.rename f).toRingHom

/-- Over a domain, neither factor introduces a variable absent from a nonzero product. -/
theorem vars_mul_eq [IsDomain A] [DecidableEq σ]
    (P Q : MvPolynomial σ A) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (P * Q).vars = P.vars ∪ Q.vars := by
  classical
  simp only [MvPolynomial.vars_def, MvPolynomial.degrees_mul_eq hP hQ, Multiset.toFinset_add]

/-- Irreducibility is preserved when the variable set is enlarged injectively. -/
theorem irreducible_rename [IsDomain A] (f : σ → τ) (hf : Function.Injective f)
    {P : MvPolynomial σ A} (hP : Irreducible P) : Irreducible (MvPolynomial.rename f P) := by
  classical
  refine ⟨?_, ?_⟩
  · intro hu
    have hm := hu.map (MvPolynomial.killCompl hf).toRingHom
    apply hP.not_isUnit
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.killCompl_rename_app] using hm
  · intro a b hab
    have hn : MvPolynomial.rename f P ≠ 0 := by
      exact (MvPolynomial.rename_injective f hf).ne (by exact hP.ne_zero)
    have ha : a ≠ 0 := by intro h; simp [h] at hab; exact hn hab
    have hb : b ≠ 0 := by intro h; simp [h] at hab; exact hn hab
    have hv : ↑(a * b).vars ⊆ Set.range f := by
      rw [← hab]
      intro t ht
      obtain ⟨s, _, hs⟩ := MvPolynomial.mem_vars_rename f P ht
      exact ⟨s, hs⟩
    rw [vars_mul_eq a b ha hb] at hv
    obtain ⟨a', ha'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range a f hf
      (fun t ht ↦ hv (Finset.mem_union_left _ ht))
    obtain ⟨b', hb'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range b f hf
      (fun t ht ↦ hv (Finset.mem_union_right _ ht))
    have hp : P = a' * b' := by
      apply MvPolynomial.rename_injective f hf
      rw [map_mul, ha', hb']
      exact hab
    rcases hP.isUnit_or_isUnit hp with hu | hu
    · left
      rw [← ha']
      exact hu.map (MvPolynomial.rename f).toRingHom
    · right
      rw [← hb']
      exact hu.map (MvPolynomial.rename f).toRingHom

/-- Splitting off one variable commutes with renaming the coefficient variables. -/
theorem optionEquivLeft_rename (f : σ → τ) (P : MvPolynomial (Option σ) A) :
    MvPolynomial.optionEquivLeft A τ (MvPolynomial.rename (Option.map f) P) =
      Polynomial.map (MvPolynomial.rename f).toRingHom (MvPolynomial.optionEquivLeft A σ P) := by
  have hh : (MvPolynomial.optionEquivLeft A τ).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (Option.map f)).toRingHom =
      (Polynomial.mapRingHom (MvPolynomial.rename f).toRingHom).comp
        (MvPolynomial.optionEquivLeft A σ).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      cases i <;> simp
  exact DFunLike.congr_fun hh P

/-- Coefficient-variable enlargement preserves univariate irreducibility. -/
theorem irreducible_polynomial_rename [IsDomain A] (f : σ → τ) (hf : Function.Injective f)
    {P : Polynomial (MvPolynomial σ A)} (hP : Irreducible P) :
    Irreducible (P.map (MvPolynomial.rename f).toRingHom) := by
  have h₁ := hP.map (MvPolynomial.optionEquivLeft A σ).symm
  have h₂ := irreducible_rename (Option.map f) (Option.map_injective hf) h₁
  have h₃ := h₂.map (MvPolynomial.optionEquivLeft A τ)
  simpa only [optionEquivLeft_rename, AlgEquiv.apply_symm_apply] using h₃

/-- Coefficient-variable enlargement reflects univariate divisibility. -/
theorem polynomial_rename_dvd_iff (f : σ → τ) (hf : Function.Injective f)
    (P Q : Polynomial (MvPolynomial σ A)) :
    P.map (MvPolynomial.rename f).toRingHom ∣ Q.map (MvPolynomial.rename f).toRingHom ↔ P ∣ Q := by
  constructor
  · intro h
    have hm := map_dvd (Polynomial.mapRingHom (MvPolynomial.killCompl hf).toRingHom) h
    change (P.map (MvPolynomial.rename f).toRingHom).map (MvPolynomial.killCompl hf).toRingHom ∣
      (Q.map (MvPolynomial.rename f).toRingHom).map (MvPolynomial.killCompl hf).toRingHom at hm
    have hh : (MvPolynomial.killCompl hf).toRingHom.comp (MvPolynomial.rename f).toRingHom =
        RingHom.id (MvPolynomial σ A) := by
      apply RingHom.ext
      intro a
      exact MvPolynomial.killCompl_rename_app hf a
    simpa only [Polynomial.map_map, hh, Polynomial.map_id] using hm
  · exact map_dvd (Polynomial.mapRingHom (MvPolynomial.rename f).toRingHom)

end Rename

section EnlargedFractionField

variable {F L σ τ : Type*} [Field F] [Field L]
  [Algebra (MvPolynomial τ F) L] [IsFractionRing (MvPolynomial τ F) L]

/-- Irreducibility survives both enlarging the coefficient variables and passing to fractions. -/
theorem enlarged_fraction_irreducible (f : σ → τ) (hf : Function.Injective f)
    {P : Polynomial (MvPolynomial σ F)} (hP : Irreducible P) (hdeg : P.natDegree ≠ 0) :
    Irreducible ((P.map (MvPolynomial.rename f).toRingHom).map
      (algebraMap (MvPolynomial τ F) L)) := by
  apply irreducible_fraction_map (irreducible_polynomial_rename f hf hP)
  simpa only [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.rename_injective f hf)]
    using hdeg

/-- Divisibility contracts through both variable enlargement and the fraction-field passage. -/
theorem enlarged_fraction_dvd_iff (f : σ → τ) (hf : Function.Injective f)
    {P : Polynomial (MvPolynomial σ F)} (hP : Irreducible P) (hdeg : P.natDegree ≠ 0)
    (Q : Polynomial (MvPolynomial σ F)) :
    (P.map (MvPolynomial.rename f).toRingHom).map (algebraMap (MvPolynomial τ F) L) ∣
      (Q.map (MvPolynomial.rename f).toRingHom).map (algebraMap (MvPolynomial τ F) L) ↔ P ∣ Q := by
  have hprim : (P.map (MvPolynomial.rename f).toRingHom).IsPrimitive :=
    (irreducible_polynomial_rename f hf hP).isPrimitive (by
      simpa only [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.rename_injective f hf)]
        using hdeg)
  rw [fraction_dvd_iff hprim, polynomial_rename_dvd_iff f hf]

end EnlargedFractionField

section GenericStrip

variable {k F L : Type*} {N : ℕ} [CommRing k] [Field F] [Field L] [CharZero L]
  [Algebra k F] [Algebra k L] [Algebra F L]
  [Algebra (MvPolynomial (Fin N × ℕ) F) L]
  [IsScalarTower k F L] [IsScalarTower F (MvPolynomial (Fin N × ℕ) F) L]
  [IsScalarTower k (MvPolynomial (Fin N × ℕ) F) L]
  [IsFractionRing (MvPolynomial (Fin N × ℕ) F) L]

/-- The generic algebraic root and the commuting strip derivations coexist in one concrete field. -/
theorem generic_strip_root
    (P : Polynomial (MvPolynomial (Fin N × ℕ) F)) (hP : Irreducible P)
    (hdeg : P.natDegree ≠ 0)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) (hN : 0 < N) :
    let p := P.map (algebraMap (MvPolynomial (Fin N × ℕ) F) L)
    let E := AdjoinRoot p
    ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      D^[N] v = AdjoinRoot.root p ∧
      (∀ a b (ha : a < N), D^[a] (H^[b] v) =
        algebraMap L E (CKStrip.jet (F := F) ⟨a, ha⟩ b)) ∧
      aeval (D^[N] v) p = 0 ∧
      (∀ Q : Polynomial (MvPolynomial (Fin N × ℕ) F),
        aeval (D^[N] v) (Q.map (algebraMap (MvPolynomial (Fin N × ℕ) F) L)) = 0 ↔ P ∣ Q) ∧
      aeval (D^[N] v) p.derivative ≠ 0 := by
  dsimp only
  let p := P.map (algebraMap (MvPolynomial (Fin N × ℕ) F) L)
  letI : Fact (Irreducible p) := ⟨irreducible_fraction_map hP hdeg⟩
  let E := AdjoinRoot p
  have : Algebra.IsSeparable L E := AlgebraicBranch.separable p
  let u : E := AdjoinRoot.root p
  let D : Derivation k E E := CKStrip.D (K := L) (N := N) δ η u
  let H : Derivation k E E := CKStrip.H (K := L) (E := E) (N := N) η
  let v : E := algebraMap L E (CKStrip.jet (F := F) ⟨0, hN⟩ 0)
  have htop : D^[N] v = u := CKStrip.strip_top_realization δ η u hN
  refine ⟨D, H, v, CKStrip.strip_commute δ η hc u, CKStrip.D_C δ η u,
    CKStrip.H_C η, htop, ?_, ?_, ?_, ?_⟩
  · intro a b ha
    exact CKStrip.strip_jet_realization δ η u hN a b ha
  · rw [htop]
    exact AlgebraicBranch.root_equation p
  · intro Q
    rw [htop]
    exact generic_root_kernel P hP hdeg Q
  · rw [htop]
    exact AlgebraicBranch.separant_nonzero p

end GenericStrip

/-- A concrete fraction field and root quotient realize the leader and all lower strip jets. -/
theorem fraction_generic_strip_root {k F : Type*} {N : ℕ}
    [CommRing k] [Field F] [CharZero F] [Algebra k F]
    (P : Polynomial (MvPolynomial (Fin N × ℕ) F)) (hP : Irreducible P)
    (hdeg : P.natDegree ≠ 0)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) (hN : 0 < N) :
    let L := FractionRing (MvPolynomial (Fin N × ℕ) F)
    let p := P.map (algebraMap (MvPolynomial (Fin N × ℕ) F) L)
    let E := AdjoinRoot p
    ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      D^[N] v = AdjoinRoot.root p ∧
      (∀ a b (ha : a < N), D^[a] (H^[b] v) =
        algebraMap L E (CKStrip.jet (F := F) ⟨a, ha⟩ b)) ∧
      aeval (D^[N] v) p = 0 ∧
      (∀ Q : Polynomial (MvPolynomial (Fin N × ℕ) F),
        aeval (D^[N] v) (Q.map (algebraMap (MvPolynomial (Fin N × ℕ) F) L)) = 0 ↔ P ∣ Q) ∧
      aeval (D^[N] v) p.derivative ≠ 0 := by
  have : CharZero (MvPolynomial (Fin N × ℕ) F) :=
    charZero_of_injective_ringHom (MvPolynomial.C_injective (Fin N × ℕ) F)
  exact generic_strip_root P hP hdeg δ η hc hN

end MakarLimanov.GenericKernel
