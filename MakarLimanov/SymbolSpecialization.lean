import MakarLimanov.DifferentialCoefficients

/-!
# Specializing symbols over a differential coefficient subalgebra

The coefficient homomorphism is allowed to have a kernel. Consequently this construction
applies to jet evaluation, unlike a homomorphism from the ambient fraction field.
-/

namespace MakarLimanov.SymbolSpecialization

open HahnSeries SymbolSeries DifferentialCoefficients

noncomputable section

variable {k F G : Type*} [Field k] [Field F] [Field G] [Algebra k F] [Algebra k G]
variable {S : Subalgebra k F}

/-- Restrict every coefficient to the subalgebra without changing the support. -/
def restrict (x : LaurentSeries F) (hx : CoefficientsIn S x) : LaurentSeries S where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (by
    intro n hn hzero
    apply hn
    exact Subtype.ext hzero)

theorem map_restrict (x : LaurentSeries F) (hx : CoefficientsIn S x) :
    (restrict x hx).map S.val.toRingHom = x := by ext; rfl

theorem map_val_injective : Function.Injective
    (fun x : LaurentSeries S ↦ x.map S.val.toRingHom) := by
  intro x y h
  ext n
  exact congrArg (fun z : LaurentSeries F ↦ z.coeff n) h

/-- Apply a possibly noninjective coefficient homomorphism only where it is defined. -/
def specialize (φ : S →ₐ[k] G) (x : LaurentSeries F) (hx : CoefficientsIn S x) :
    LaurentSeries G := (restrict x hx).map φ.toRingHom

@[simp] theorem specialize_coeff (φ : S →ₐ[k] G) (x : LaurentSeries F)
    (hx : CoefficientsIn S x) (n : ℤ) : (specialize φ x hx).coeff n = φ ⟨x.coeff n, hx n⟩ := rfl

theorem specialize_zero (φ : S →ₐ[k] G) :
    specialize φ 0 DifferentialCoefficients.zero = 0 := by
  ext n
  exact map_zero φ

theorem specialize_add (φ : S →ₐ[k] G) (x y : LaurentSeries F)
    (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) :
    specialize φ (x + y) (DifferentialCoefficients.add hx hy) =
      specialize φ x hx + specialize φ y hy := by
  ext n
  change φ (⟨x.coeff n, hx n⟩ + ⟨y.coeff n, hy n⟩ : S) = _
  exact map_add φ _ _

theorem specialize_mul (φ : S →ₐ[k] G) (x y : LaurentSeries F)
    (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) :
    specialize φ (x * y) (DifferentialCoefficients.mul hx hy) =
      specialize φ x hx * specialize φ y hy := by
  have hr : restrict (x * y) (DifferentialCoefficients.mul hx hy) =
      restrict x hx * restrict y hy := by
    apply map_val_injective
    change (restrict (x * y) _).map S.val.toRingHom =
      (restrict x hx * restrict y hy).map S.val.toRingHom
    have hm : (restrict x hx * restrict y hy).map S.val.toRingHom =
        (restrict x hx).map S.val.toRingHom * (restrict y hy).map S.val.toRingHom :=
      HahnSeries.map_mul S.val.toRingHom.toNonUnitalRingHom
    rw [map_restrict, hm, map_restrict, map_restrict]
  unfold specialize
  rw [hr]
  exact HahnSeries.map_mul φ.toRingHom.toNonUnitalRingHom

theorem specialize_single (φ : S →ₐ[k] G) (n : ℤ) (a : S) :
    specialize φ (HahnSeries.single n a.val) (DifferentialCoefficients.single n a.property) =
      HahnSeries.single n (φ a) := by
  ext m
  by_cases hm : m = n
  · subst m
    simp
  · simp only [specialize_coeff, coeff_single_of_ne hm]
    exact map_zero φ

theorem specialize_smul (φ : S →ₐ[k] G) (a : S) (x : LaurentSeries F)
    (hx : CoefficientsIn S x) :
    specialize φ (a.val • x) (DifferentialCoefficients.smul a.property hx) =
      φ a • specialize φ x hx := by
  ext n
  change φ (a * ⟨x.coeff n, hx n⟩) = _
  exact map_mul φ _ _

theorem lowerBound (φ : S →ₐ[k] G) (x : LaurentSeries F) (hx : CoefficientsIn S x)
    {b : ℤ} (hb : LowerBound b x) : LowerBound b (specialize φ x hx) := by
  intro n hn
  change φ ⟨x.coeff n, hx n⟩ = 0
  have hz : (⟨x.coeff n, hx n⟩ : S) = 0 := Subtype.ext (hb n hn)
  rw [hz, map_zero]

theorem specialize_coefficientDerivation (φ : S →ₐ[k] G)
    (d : Derivation k F F) (d' : Derivation k G G) (hd : ∀ a ∈ S, d a ∈ S)
    (hφ : ∀ a : S, φ ⟨d a, hd a a.property⟩ = d' (φ a))
    (x : LaurentSeries F) (hx : CoefficientsIn S x) :
    specialize φ (SymbolSeries.coefficientDerivation d x)
        (DifferentialCoefficients.coefficientDerivation d hd hx) =
      SymbolSeries.coefficientDerivation d' (specialize φ x hx) := by
  ext n
  exact hφ ⟨x.coeff n, hx n⟩

theorem specialize_deltaOperator (φ : S →ₐ[k] G) (p : ℕ)
    (η : Derivation k F F) (η' : Derivation k G G) (hη : ∀ a ∈ S, η a ∈ S)
    (hφ : ∀ a : S, φ ⟨η a, hη a a.property⟩ = η' (φ a))
    (x : LaurentSeries F) (hx : CoefficientsIn S x) :
    specialize φ (SymbolSeries.deltaOperator p η x)
        (DifferentialCoefficients.deltaOperator p η hη hx) =
      SymbolSeries.deltaOperator p η' (specialize φ x hx) := by
  ext n
  let a : S := ⟨x.coeff (n - p), hx (n - p)⟩
  have hh : (⟨(SymbolSeries.deltaOperator p η x).coeff n,
      DifferentialCoefficients.deltaOperator p η hη hx n⟩ : S) =
      ⟨η a, hη a a.property⟩ - algebraMap k S ((p : k)⁻¹) * (n - p : ℤ) * a := by
    apply Subtype.ext
    simp [a, deltaOperator_coeff]
  rw [specialize_coeff, hh, deltaOperator_coeff]
  simp only [map_sub, map_mul, map_intCast, AlgHom.commutes, map_inv₀, map_natCast, hφ]
  rfl

theorem specialize_iterate (φ : S →ₐ[k] G)
    (T : LaurentSeries F → LaurentSeries F) (U : LaurentSeries G → LaurentSeries G)
    (hT : ∀ x, CoefficientsIn S x → CoefficientsIn S (T x))
    (hTU : ∀ x hx, specialize φ (T x) (hT x hx) = U (specialize φ x hx))
    (x : LaurentSeries F) (hx : CoefficientsIn S x) (j : ℕ) :
    specialize φ (T^[j] x) (DifferentialCoefficients.iterate hT hx j) =
      U^[j] (specialize φ x hx) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    rw [hTU _ (DifferentialCoefficients.iterate hT hx j), ih]

theorem specialize_starTerm (φ : S →ₐ[k] G) (p : ℕ)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hφδ : ∀ a : S, φ ⟨δ a, hδ a a.property⟩ = δ' (φ a))
    (hφη : ∀ a : S, φ ⟨η a, hη a a.property⟩ = η' (φ a))
    (x y : LaurentSeries F) (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) (j : ℕ) :
    specialize φ (SymbolSeries.starTerm p δ η x y j)
        (DifferentialCoefficients.starTerm p δ η hδ hη hx hy j) =
      SymbolSeries.starTerm p δ' η' (specialize φ x hx) (specialize φ y hy) j := by
  have hΔ := specialize_iterate φ (SymbolSeries.deltaOperator p η)
    (SymbolSeries.deltaOperator p η') (fun _ h ↦ DifferentialCoefficients.deltaOperator p η hη h)
    (fun x hx ↦ specialize_deltaOperator φ p η η' hη hφη x hx) x hx j
  have hD := specialize_iterate φ (SymbolSeries.coefficientDerivation δ)
    (SymbolSeries.coefficientDerivation δ')
    (fun _ h ↦ DifferentialCoefficients.coefficientDerivation δ hδ h)
    (fun y hy ↦ specialize_coefficientDerivation φ δ δ' hδ hφδ y hy) y hy j
  have hs := specialize_smul φ (algebraMap k S ((j.factorial : k)⁻¹))
    ((SymbolSeries.deltaOperator p η)^[j] x * (SymbolSeries.coefficientDerivation δ)^[j] y)
    (DifferentialCoefficients.mul
      (DifferentialCoefficients.iterate (fun _ h ↦
        DifferentialCoefficients.deltaOperator p η hη h) hx j)
      (DifferentialCoefficients.iterate (fun _ h ↦
        DifferentialCoefficients.coefficientDerivation δ hδ h) hy j))
  simp only [AlgHom.commutes, map_inv₀, map_natCast, Subalgebra.coe_algebraMap] at hs
  change specialize φ ((j.factorial : F)⁻¹ • _) _ = _
  rw [hs, specialize_mul φ _ _
    (DifferentialCoefficients.iterate (fun _ h ↦
      DifferentialCoefficients.deltaOperator p η hη h) hx j)
    (DifferentialCoefficients.iterate (fun _ h ↦
      DifferentialCoefficients.coefficientDerivation δ hδ h) hy j), hΔ, hD]
  rfl

/-- A common support bound gives the same finite sum before and after specialization. -/
theorem starProduct_coeff_of_bounds (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) {b c : ℤ} (hx : LowerBound b x) (hy : LowerBound c y) (n : ℤ) :
    (SymbolSeries.starProduct p hp δ η x y).coeff n =
      ∑ j ∈ Finset.range ((n - (b + c)).toNat + 1),
        (SymbolSeries.starTerm p δ η x y j).coeff n := by
  apply SummableFamily.coeff_hsum_eq_sum_of_subset
  intro j hj
  change (SymbolSeries.starTerm p δ η x y j).coeff n ≠ 0 at hj
  have hn : b + c + (p : ℤ) * j ≤ n := by
    by_contra! hn
    exact hj (starTerm_lowerBound p δ η hx hy j n hn)
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hj' : (0 : ℤ) ≤ j := by omega
  have h : (j : ℤ) ≤ n - (b + c) := by nlinarith
  change j ∈ Finset.range ((n - (b + c)).toNat + 1)
  rw [Finset.mem_range]
  omega

/-- Specialization preserves the actual infinite star product, even when coefficients vanish. -/
theorem specialize_starProduct (φ : S →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hφδ : ∀ a : S, φ ⟨δ a, hδ a a.property⟩ = δ' (φ a))
    (hφη : ∀ a : S, φ ⟨η a, hη a a.property⟩ = η' (φ a))
    (x y : LaurentSeries F) (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) :
    specialize φ (SymbolSeries.starProduct p hp δ η x y)
        (DifferentialCoefficients.starProduct p hp δ η hδ hη hx hy) =
      SymbolSeries.starProduct p hp δ' η' (specialize φ x hx) (specialize φ y hy) := by
  ext n
  have hh : (⟨(SymbolSeries.starProduct p hp δ η x y).coeff n,
      DifferentialCoefficients.starProduct p hp δ η hδ hη hx hy n⟩ : S) =
      ∑ j ∈ Finset.range ((n - (x.order + y.order)).toNat + 1),
        ⟨(SymbolSeries.starTerm p δ η x y j).coeff n,
          DifferentialCoefficients.starTerm p δ η hδ hη hx hy j n⟩ := by
    apply Subtype.ext
    simpa using starProduct_coeff_finite p hp δ η x y n
  rw [specialize_coeff, hh, map_sum,
    starProduct_coeff_of_bounds p hp δ' η' _ _
      (lowerBound φ x hx (lowerBound_order x)) (lowerBound φ y hy (lowerBound_order y))]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun z : LaurentSeries G ↦ z.coeff n)
    (specialize_starTerm φ p δ η δ' η' hδ hη hφδ hφη x y hx hy j)

variable [CharZero F] [CharZero G]

open SymbolSeries.StarSeries

/-- Specialization commutes with ordered evaluation of every free polynomial. -/
theorem specialize_evaluate {ι : Type*} (φ : S →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (hc : Function.Commute δ η) (hc' : Function.Commute δ' η')
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hφδ : ∀ a : S, φ ⟨δ a, hδ a a.property⟩ = δ' (φ a))
    (hφη : ∀ a : S, φ ⟨η a, hη a a.property⟩ = η' (φ a))
    (X : ι → StarSeries p hp δ η hc) (hX : ∀ i, CoefficientsIn S (toSeries (X i)))
    (f : FreeAlgebra k ι) :
    specialize φ (toSeries (FreeAlgebra.lift k X f))
        (DifferentialCoefficients.evaluate p hp δ η hc hδ hη X hX f) =
      toSeries (FreeAlgebra.lift k
        (fun i ↦ ofSeries (hp := hp) (h := hc') (specialize φ (toSeries (X i)) (hX i))) f) := by
  induction f with
  | grade0 a =>
    have hh := specialize_single φ 0 (algebraMap k S a)
    simpa using hh
  | grade1 i => simp
  | add f g hf hg =>
    simp only [map_add, toSeries_add]
    rw [specialize_add φ _ _
      (DifferentialCoefficients.evaluate p hp δ η hc hδ hη X hX f)
      (DifferentialCoefficients.evaluate p hp δ η hc hδ hη X hX g), hf, hg]
  | mul f g hf hg =>
    simp only [map_mul, toSeries_mul]
    rw [specialize_starProduct φ p hp δ η δ' η' hδ hη hφδ hφη _ _
      (DifferentialCoefficients.evaluate p hp δ η hc hδ hη X hX f)
      (DifferentialCoefficients.evaluate p hp δ η hc hδ hη X hX g), hf, hg]

/-- A nonzero specialized evaluation certifies that the original symbolic evaluation is nonzero. -/
theorem evaluate_ne_zero_of_specialize {ι : Type*} (φ : S →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (hc : Function.Commute δ η) (hc' : Function.Commute δ' η')
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hφδ : ∀ a : S, φ ⟨δ a, hδ a a.property⟩ = δ' (φ a))
    (hφη : ∀ a : S, φ ⟨η a, hη a a.property⟩ = η' (φ a))
    (X : ι → StarSeries p hp δ η hc) (hX : ∀ i, CoefficientsIn S (toSeries (X i)))
    (f : FreeAlgebra k ι)
    (hf : toSeries (FreeAlgebra.lift k
      (fun i ↦ ofSeries (hp := hp) (h := hc') (specialize φ (toSeries (X i)) (hX i))) f) ≠ 0) :
    toSeries (FreeAlgebra.lift k X f) ≠ 0 := by
  intro hz
  apply hf
  rw [← specialize_evaluate φ p hp δ η δ' η' hc hc' hδ hη hφδ hφη X hX f]
  simp only [hz, specialize_zero]

end

end MakarLimanov.SymbolSpecialization
