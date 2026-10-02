import MakarLimanov.DifferentialExtension
import MakarLimanov.PolynomialDerivations
import MakarLimanov.LocalizedDerivations
import Mathlib.Tactic

/-! Commuting derivations on a rational strip and its separable algebraic extensions. -/

namespace MakarLimanov.CKStrip
open PolynomialDerivations LocalizedDerivations
section Ext
variable {k R S E : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing E]
  [Algebra k S] [Algebra k E] [Algebra S E] [IsScalarTower k S E]
  [Algebra R S]
lemma derivation_ext_localization (M : Submonoid R) [IsLocalization M S]
    (d₁ d₂ : Derivation k S E)
    (h : ∀ a : R, d₁ (algebraMap R S a) = d₂ (algebraMap R S a)) : d₁ = d₂ := by
  have he : (derivationDual d₁).toRingHom = (derivationDual d₂).toRingHom := by
    apply IsLocalization.ringHom_ext M
    ext a
    · rfl
    · exact h a
  ext a
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun he a)
end Ext
section PolyExt
variable {k F E : Type*} [CommRing k] [CommRing F] [CommRing E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
variable {σ : Type*} [Algebra (MvPolynomial σ F) E]
  [IsScalarTower F (MvPolynomial σ F) E]
  [IsScalarTower k (MvPolynomial σ F) E]
omit [Algebra F E] [IsScalarTower k F E] [IsScalarTower F (MvPolynomial σ F) E] in
lemma derivation_ext_mv (d₁ d₂ : Derivation k (MvPolynomial σ F) E)
    (hC : ∀ a : F, d₁ (MvPolynomial.C a) = d₂ (MvPolynomial.C a))
    (hX : ∀ i : σ, d₁ (MvPolynomial.X i) = d₂ (MvPolynomial.X i)) : d₁ = d₂ := by
  have he : (derivationDual d₁).toRingHom = (derivationDual d₂).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      ext
      · rfl
      · exact hC a
    · intro i
      ext
      · rfl
      · exact hX i
  ext a
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun he a)
end PolyExt
section Rational
variable {k F K E : Type*} {σ : Type*} [CommRing k] [Field F] [Field K] [Field E]
  [Algebra k F] [Algebra k K] [Algebra k E] [Algebra F K] [Algebra F E] [Algebra K E]
  [Algebra (MvPolynomial σ F) K] [Algebra (MvPolynomial σ F) E]
  [IsScalarTower k F K] [IsScalarTower k F E] [IsScalarTower k K E]
  [IsScalarTower F K E]
  [IsScalarTower F (MvPolynomial σ F) K] [IsScalarTower F (MvPolynomial σ F) E]
  [IsScalarTower k (MvPolynomial σ F) K] [IsScalarTower k (MvPolynomial σ F) E]
  [IsScalarTower (MvPolynomial σ F) K E]
  [IsFractionRing (MvPolynomial σ F) K]
noncomputable def rationalDerivation (d : Derivation k F E) (dx : σ → E) :
    Derivation k K E :=
  extendLocalizedDerivation (nonZeroDivisors (MvPolynomial σ F)) (mvDerivation d dx)
omit [Algebra F K] [IsScalarTower k F K] [IsScalarTower F K E] [IsScalarTower F (MvPolynomial σ F) K] in
lemma rationalDerivation_poly (d : Derivation k F E) (dx : σ → E)
    (p : MvPolynomial σ F) :
    rationalDerivation (K := K) d dx (algebraMap (MvPolynomial σ F) K p) =
      mvDerivation d dx p :=
  extendLocalizedDerivation_apply _ _ _
omit [IsScalarTower k F K] [IsScalarTower F K E] in
lemma rationalDerivation_C (d : Derivation k F E) (dx : σ → E) (a : F) :
    rationalDerivation (K := K) d dx (algebraMap F K a) = d a := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial σ F) K]
  exact (rationalDerivation_poly d dx _).trans (mvDerivation_C d dx a)
omit [Algebra F K] [IsScalarTower k F K] [IsScalarTower F K E] [IsScalarTower F (MvPolynomial σ F) K] in
lemma rationalDerivation_X (d : Derivation k F E) (dx : σ → E) (i : σ) :
    rationalDerivation (K := K) d dx
      (algebraMap (MvPolynomial σ F) K (MvPolynomial.X i)) = dx i :=
  (rationalDerivation_poly d dx _).trans (mvDerivation_X d dx i)
omit [IsScalarTower k F K] [IsScalarTower F K E] in
omit [Algebra F E] [IsScalarTower k F E] [IsScalarTower F (MvPolynomial σ F) E] in
lemma derivation_ext_rational (d₁ d₂ : Derivation k K E)
    (hC : ∀ a : F, d₁ (algebraMap F K a) = d₂ (algebraMap F K a))
    (hX : ∀ i : σ, d₁ (algebraMap (MvPolynomial σ F) K (MvPolynomial.X i)) =
      d₂ (algebraMap (MvPolynomial σ F) K (MvPolynomial.X i))) : d₁ = d₂ := by
  apply derivation_ext_localization (nonZeroDivisors (MvPolynomial σ F))
  have he : d₁.compAlgebraMap (MvPolynomial σ F) = d₂.compAlgebraMap (MvPolynomial σ F) := by
    apply derivation_ext_mv
    · intro a
      change d₁ (algebraMap (MvPolynomial σ F) K (algebraMap F (MvPolynomial σ F) a)) =
        d₂ (algebraMap (MvPolynomial σ F) K (algebraMap F (MvPolynomial σ F) a))
      simpa only [← IsScalarTower.algebraMap_apply] using hC a
    · exact hX
  exact DFunLike.congr_fun he
end Rational
section Strip
variable {k F K E : Type*} {N : ℕ} [CommRing k] [Field F] [Field K] [Field E]
  [Algebra k F] [Algebra k K] [Algebra k E] [Algebra F K] [Algebra F E] [Algebra K E]
  [Algebra (MvPolynomial (Fin N × ℕ) F) K] [Algebra (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k F K] [IsScalarTower k F E] [IsScalarTower k K E]
  [IsScalarTower F K E]
  [IsScalarTower F (MvPolynomial (Fin N × ℕ) F) K]
  [IsScalarTower F (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (Fin N × ℕ) F) K]
  [IsScalarTower k (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower (MvPolynomial (Fin N × ℕ) F) K E]
  [IsFractionRing (MvPolynomial (Fin N × ℕ) F) K]
  [Algebra.IsSeparable K E]
open MakarLimanov.DifferentialExtension
noncomputable def jet (i : Fin N) (b : ℕ) : K :=
  algebraMap (MvPolynomial (Fin N × ℕ) F) K (MvPolynomial.X (i, b))
noncomputable def Hbase (η : Derivation k F F) : Derivation k K K :=
  rationalDerivation (k := k) (F := F) (K := K) (E := K) (σ := Fin N × ℕ)
    ((Algebra.linearMap F K).compDer η)
    (fun (i,b) ↦ jet (F := F) i (b+1))
noncomputable def H (η : Derivation k F F) : Derivation k E E :=
  extendDerivation ((Algebra.linearMap K E).compDer (Hbase (N := N) η))
omit [Algebra (MvPolynomial (Fin N × ℕ) F) E] [IsScalarTower k F E]
  [IsScalarTower F (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower (MvPolynomial (Fin N × ℕ) F) K E] in
lemma H_C (η : Derivation k F F) (a : F) :
    H (K := K) (E := E) (N := N) η (algebraMap F E a) = algebraMap F E (η a) := by
  rw [IsScalarTower.algebraMap_apply F K E]
  simp [H, extendDerivation_apply, LinearMap.compDer, Hbase, rationalDerivation_C,
    IsScalarTower.algebraMap_apply F K E]
omit [Algebra F E] [Algebra (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k F E] [IsScalarTower F K E]
  [IsScalarTower F (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower (MvPolynomial (Fin N × ℕ) F) K E] in
lemma H_jet (η : Derivation k F F) (i : Fin N) (b : ℕ) :
    H (K := K) (E := E) (N := N) η (algebraMap K E (jet (F := F) i b)) =
      algebraMap K E (jet (F := F) i (b+1)) := by
  simp [H, extendDerivation_apply, LinearMap.compDer, Hbase, jet, rationalDerivation_X]
noncomputable def Dvalues (η : Derivation k F F) (u : E) (ib : Fin N × ℕ) : E :=
  if hi : ib.1.val + 1 < N then
    algebraMap K E (jet (F := F) ⟨ib.1.val + 1, hi⟩ ib.2)
  else (H (K := K) (E := E) (N := N) η)^[ib.2] u
noncomputable def Dbase (δ η : Derivation k F F) (u : E) : Derivation k K E :=
  rationalDerivation (k := k) (F := F) (K := K) (E := E) (σ := Fin N × ℕ)
    ((Algebra.linearMap F E).compDer δ)
    (Dvalues (K := K) (N := N) η u)
noncomputable def D (δ η : Derivation k F F) (u : E) : Derivation k E E :=
  extendDerivation (Dbase (K := K) (N := N) δ η u)
lemma D_C (δ η : Derivation k F F) (u : E) (a : F) :
    D (K := K) (N := N) δ η u (algebraMap F E a) = algebraMap F E (δ a) := by
  rw [IsScalarTower.algebraMap_apply F K E]
  simp [D, extendDerivation_apply, Dbase, rationalDerivation_C, LinearMap.compDer]
omit [IsScalarTower F K E] in
lemma D_jet (δ η : Derivation k F F) (u : E) (i : Fin N) (b : ℕ) :
    D (K := K) (N := N) δ η u (algebraMap K E (jet (F := F) i b)) =
      Dvalues (K := K) η u (i,b) := by
  simp [D, extendDerivation_apply, Dbase, jet, rationalDerivation_X]
lemma strip_commute (δ η : Derivation k F F) (hc : Function.Commute δ η) (u : E) :
    Function.Commute (D (K := K) (N := N) δ η u) (H (K := K) (E := E) (N := N) η) := by
  apply commute_of_commute_on_base (K := K)
  have hz : (⁅D (K := K) (N := N) δ η u, H (K := K) (E := E) (N := N) η⁆).compAlgebraMap K = 0 := by
    apply derivation_ext_rational (F := F) (σ := Fin N × ℕ)
    · intro a
      change D (K := K) (N := N) δ η u (H (K := K) (E := E) (N := N) η
        (algebraMap K E (algebraMap F K a))) -
        H (K := K) (E := E) (N := N) η (D (K := K) (N := N) δ η u
        (algebraMap K E (algebraMap F K a))) = 0
      rw [← IsScalarTower.algebraMap_apply F K E]
      simp only [H_C, D_C, hc a, sub_self]
    · rintro ⟨i,b⟩
      change D (K := K) (N := N) δ η u (H (K := K) (E := E) (N := N) η
        (algebraMap K E (jet (F := F) i b))) -
        H (K := K) (E := E) (N := N) η (D (K := K) (N := N) δ η u (algebraMap K E (jet (F := F) i b))) = 0
      rw [H_jet, D_jet, D_jet]
      simp only [Dvalues]
      split_ifs with hi
      · rw [H_jet, sub_self]
      · rw [Function.iterate_succ_apply', sub_self]
  intro a
  have ha := DFunLike.congr_fun hz a
  simpa [Derivation.compAlgebraMap, Derivation.commutator_apply, sub_eq_zero] using ha
omit [Algebra F E] [Algebra (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k F E] [IsScalarTower F K E]
  [IsScalarTower F (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (Fin N × ℕ) F) E]
  [IsScalarTower (MvPolynomial (Fin N × ℕ) F) K E] in
lemma H_iterate_jet_zero (η : Derivation k F F) (i : Fin N) (b : ℕ) :
    (H (K := K) (E := E) (N := N) η)^[b] (algebraMap K E (jet (F := F) i 0)) =
      algebraMap K E (jet (F := F) i b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ_apply', ih, H_jet]
omit [IsScalarTower F K E] in
lemma D_iterate_jet_zero (δ η : Derivation k F F) (u : E) (hN : 0 < N)
    (a b : ℕ) (ha : a < N) :
    (D (K := K) (N := N) δ η u)^[a] (algebraMap K E (jet (F := F) ⟨0,hN⟩ b)) =
      algebraMap K E (jet (F := F) ⟨a,ha⟩ b) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have ha' : a < N := Nat.lt_trans (Nat.lt_succ_self a) ha
    rw [Function.iterate_succ_apply', ih ha', D_jet]
    simp [Dvalues, ha]
omit [IsScalarTower F K E] in
lemma strip_jet_realization (δ η : Derivation k F F) (u : E) (hN : 0 < N)
    (a b : ℕ) (ha : a < N) :
    (D (K := K) (N := N) δ η u)^[a]
      ((H (K := K) (E := E) (N := N) η)^[b]
        (algebraMap K E (jet (F := F) ⟨0,hN⟩ 0))) =
      algebraMap K E (jet (F := F) ⟨a,ha⟩ b) := by
  rw [H_iterate_jet_zero, D_iterate_jet_zero δ η u hN a b ha]
omit [IsScalarTower F K E] in
lemma strip_top_realization (δ η : Derivation k F F) (u : E) (hN : 0 < N) :
    (D (K := K) (N := N) δ η u)^[N]
      (algebraMap K E (jet (F := F) ⟨0,hN⟩ 0)) = u := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hN)
  have hm' : m < N := by omega
  calc
    _ = (D (K := K) (N := N) δ η u)^[m+1]
        (algebraMap K E (jet (F := F) ⟨0,hN⟩ 0)) :=
      congrArg (fun n ↦ (D (K := K) (N := N) δ η u)^[n]
        (algebraMap K E (jet (F := F) ⟨0,hN⟩ 0))) hm
    _ = u := by
      rw [Function.iterate_succ_apply', D_iterate_jet_zero δ η u hN m 0 hm', D_jet]
      simp [Dvalues, show ¬ m + 1 < N by omega]
end Strip

end MakarLimanov.CKStrip
