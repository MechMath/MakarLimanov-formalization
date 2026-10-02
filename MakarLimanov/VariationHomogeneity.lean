import MakarLimanov.VariationCoefficients
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneity of the actual variation coefficients

Scaling a generic differential indeterminate by two scales every mixed jet by
two and its `j`th variation by `2^j`. Comparing monomial coefficients forces
the universal coefficient polynomial to be homogeneous of degree `j`.
-/

namespace MakarLimanov.VariationHomogeneity

open MvPolynomial SymbolSeries SymbolSeries.StarSeries VariationCoefficients

noncomputable section

/-- Simultaneously scale every polynomial variable. -/
def dilation {F σ : Type*} [CommSemiring F] (a : F) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun i ↦ C a * X i)

theorem dilation_monomial {F σ : Type*} [CommSemiring F]
    (a r : F) (d : σ →₀ ℕ) :
    dilation a (monomial d r) = a ^ d.degree • monomial d r := by
  classical
  simp only [dilation, aeval_monomial, algebraMap_eq, mul_pow, Finsupp.prod,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [MvPolynomial.smul_eq_C_mul, monomial_eq, Finsupp.prod]
  change C r * (C (a ^ d.degree) * _) = _
  ring

theorem dilation_coeff {F σ : Type*} [CommSemiring F]
    (a : F) (P : MvPolynomial σ F) (d : σ →₀ ℕ) :
    (dilation a P).coeff d = a ^ d.degree * P.coeff d := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [dilation_monomial]
    simp only [coeff_smul, smul_eq_mul, coeff_monomial]
    split_ifs with h
    · subst e; rfl
    · simp
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]

/-- In characteristic zero, covariance under doubling detects homogeneous degree. -/
theorem isHomogeneous_of_dilation_two {F σ : Type*} [Field F] [CharZero F]
    (P : MvPolynomial σ F) (j : ℕ) (hP : dilation (2 : F) P = (2 : F) ^ j • P) :
    P.IsHomogeneous j := by
  intro d hd
  change (Finsupp.weight (fun _ : σ ↦ 1)) d = j
  rw [← Finsupp.degree_eq_weight_one]
  have he := congrArg (fun Q : MvPolynomial σ F ↦ Q.coeff d) hP
  dsimp only at he
  rw [dilation_coeff, coeff_smul, smul_eq_mul] at he
  have hp : (2 : F) ^ d.degree = (2 : F) ^ j :=
    (mul_right_inj' hd).mp (by simpa [mul_comm] using he)
  have hn : (2 : ℕ) ^ d.degree = 2 ^ j := by exact_mod_cast hp
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hn

/-- Natural-number scaling of the perturbation has the exact variation degree. -/
theorem variation_nsmul {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
    (f : FreeAlgebra k Bool) (x z v : A) (r j : ℕ) :
    Variations.variation f x z (r • v) j = r ^ j • Variations.variation f x z v j := by
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    Variations.variation_central_mul f x z v (r : A) (fun a ↦ Nat.cast_commute r a |>.symm) j

theorem symbolVariation_nsmul {k E : Type*} [Field k] [Field E] [Algebra k E] [CharZero E]
    {p : ℕ} {hp : 0 < p} {δ η : Derivation k E E} {hc : Function.Commute δ η}
    (f : FreeAlgebra k Bool) (z v : LaurentSeries E) (r j : ℕ) :
    SymbolVariations.variation (hp := hp) (h := hc) f z (r • v) j =
      r ^ j • SymbolVariations.variation (hp := hp) (h := hc) f z v j := by
  let toAdd : StarSeries p hp δ η hc →+ LaurentSeries E :=
    { toFun := toSeries, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hv : ofSeries (hp := hp) (h := hc) (r • v) = r • ofSeries v := rfl
  unfold SymbolVariations.variation
  rw [hv, variation_nsmul]
  exact toAdd.map_nsmul _ _

section Generic

open GenericJets JetSpecialization

variable {k F E G : Type*} [Field k] [Field F] [Field E] [Field G] [CharZero F]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero E] [Algebra k G] [Algebra F G] [IsScalarTower k F G] [CharZero G]

omit [CharZero E] in
/-- Natural scaling commutes with every iterate of a derivation. -/
theorem iterate_derivation_nsmul (D : Derivation k E E) (a : E) (r m : ℕ) :
    D^[m] (r • a) = r • D^[m] a := by
  induction m with
  | zero => rfl
  | succ m hm => simp only [Function.iterate_succ_apply', hm, map_nsmul]

omit [CharZero F] [CharZero E] in
/-- Doubling the generic element evaluates a jet polynomial by simultaneous dilation. -/
theorem eval_mixed_nsmul (δ η : Derivation k F F) (r : ℕ)
    (P : MvPolynomial (ℕ × ℕ) F) :
    MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
      (GenericJets.delta (E := E) δ)^[ij.1]
        ((GenericJets.eta η)^[ij.2] (r • jet (F := F) 0 0))) P =
      algebraMap (MvPolynomial (ℕ × ℕ) F) E (dilation (r : F) P) := by
  simp only [iterate_derivation_nsmul, mixed_jet]
  have he : MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ r • jet (F := F) (E := E) ij.1 ij.2) =
      (IsScalarTower.toAlgHom F (MvPolynomial (ℕ × ℕ) F) E).comp (dilation (r : F)) := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp [dilation, jet, nsmul_eq_mul]
  exact DFunLike.congr_fun he P

omit [CharZero F] in
/-- Any actual generic coefficient representative obeys the exact variation scaling law. -/
theorem representative_dilation (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ)
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericVariation (E := E) δ η hc p hp q z f j).coeff n) (r : ℕ) :
    dilation (r : F) P = (r : F) ^ j • P := by
  obtain ⟨Q, hQ, hvalue⟩ := exists_universal_variation_coefficient (E := E) (G := E)
    δ η hc p hp q z f j n
  have he : P = Q := coefficient_representative_unique _ P Q hP hQ
  subst Q
  have hs := hvalue (GenericJets.delta δ) (GenericJets.eta η) (GenericJets.commute δ η hc)
    (delta_base δ) (eta_base η) (r • jet (F := F) (E := E) 0 0)
  rw [eval_mixed_nsmul] at hs
  have hv : HahnSeries.single q (r • jet (F := F) (E := E) 0 0) =
      r • HahnSeries.single q (jet (F := F) (E := E) 0 0) := by
    ext m
    by_cases hm : m = q
    · subst m
      rw [HahnSeries.coeff_smul, HahnSeries.coeff_single_same]
      simp only [HahnSeries.coeff_single_same]
    · rw [HahnSeries.coeff_single_of_ne hm, HahnSeries.coeff_smul,
        HahnSeries.coeff_single_of_ne hm, smul_zero]
  rw [hv, symbolVariation_nsmul] at hs
  apply IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E
  rw [hs, HahnSeries.coeff_nsmul]
  change r ^ j • (genericVariation (E := E) δ η hc p hp q z f j).coeff n = _
  rw [← hP, MvPolynomial.smul_eq_C_mul, map_mul, map_pow]
  simp [nsmul_eq_mul]

/-- Every universal coefficient of the `j`th variation is homogeneous of ordinary degree `j`. -/
theorem representative_isHomogeneous (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ)
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericVariation (E := E) δ η hc p hp q z f j).coeff n) :
    P.IsHomogeneous j := by
  exact isHomogeneous_of_dilation_two P j
    (representative_dilation δ η hc p hp q z f j n P hP 2)

/-- Pack the universal coefficient and its homogeneous-degree certificate together. -/
theorem exists_homogeneous_universal_variation_coefficient
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F, P.IsHomogeneous j ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericVariation (E := E) δ η hc p hp q z f j).coeff n ∧
      ∀ (D H : Derivation k G G) (hDH : Function.Commute D H),
        (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) →
        (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) → ∀ w : G,
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
          (SymbolVariations.variation (hp := hp) (h := hDH) f
            (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j).coeff n := by
  obtain ⟨P, hP, hspecial⟩ :=
    exists_universal_variation_coefficient (E := E) (G := G) δ η hc p hp q z f j n
  exact ⟨P, representative_isHomogeneous δ η hc p hp q z f j n P hP, hP, hspecial⟩

end Generic

end

end MakarLimanov.VariationHomogeneity
