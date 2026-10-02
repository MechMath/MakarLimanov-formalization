import MakarLimanov.JetSpecialization

/-!
# Universal polynomial coefficients of actual symbol variations

Specialization on a stable coefficient subalgebra induces a homomorphism on its
star algebra. It therefore preserves every variation. Applied to generic jets,
this gives one polynomial representative valid at every compatible differential
specialization, for a perturbation around an arbitrary base symbol.
-/

namespace MakarLimanov.VariationCoefficients

open SymbolSeries SymbolSeries.StarSeries DifferentialCoefficients SymbolSpecialization

noncomputable section

section CoefficientAlgebra

variable {k F G : Type*} [Field k] [Field F] [Field G]
  [Algebra k F] [Algebra k G] [CharZero F] [CharZero G]
  {S : Subalgebra k F}

/-- Symbols over a differential coefficient subalgebra form a star subalgebra. -/
def starSubalgebra (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S) :
    Subalgebra k (StarSeries p hp δ η hc) where
  carrier := {U | CoefficientsIn S (toSeries U)}
  mul_mem' := fun hx hy ↦ DifferentialCoefficients.starProduct p hp δ η hδ hη hx hy
  one_mem' := DifferentialCoefficients.single 0 S.one_mem
  add_mem' := fun hx hy ↦ DifferentialCoefficients.add hx hy
  zero_mem' := DifferentialCoefficients.zero
  algebraMap_mem' := fun a ↦ DifferentialCoefficients.single 0 (S.algebraMap_mem a)

/-- A differential coefficient specialization induces a homomorphism of star algebras. -/
def specializeAlgHom (φ : S →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (D H : Derivation k G G)
    (hc : Function.Commute δ η) (hDH : Function.Commute D H)
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hφδ : ∀ a : S, φ ⟨δ a, hδ a a.property⟩ = D (φ a))
    (hφη : ∀ a : S, φ ⟨η a, hη a a.property⟩ = H (φ a)) :
    starSubalgebra p hp δ η hc hδ hη →ₐ[k] StarSeries p hp D H hDH where
  toFun U := ofSeries (specialize φ (toSeries U.val) U.property)
  map_zero' := specialize_zero φ
  map_one' := by
    have hh := specialize_single φ 0 (1 : S)
    simpa using hh
  map_add' U V := specialize_add φ _ _ U.property V.property
  map_mul' U V := specialize_starProduct φ p hp δ η D H hδ hη hφδ hφη
    _ _ U.property V.property
  commutes' a := by
    have hh := specialize_single φ 0 (algebraMap k S a)
    simpa using hh

/-- Differential coefficient specialization preserves each actual variation. -/
theorem specialize_variation (φ : S →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (D H : Derivation k G G)
    (hc : Function.Commute δ η) (hDH : Function.Commute D H)
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hφδ : ∀ a : S, φ ⟨δ a, hδ a a.property⟩ = D (φ a))
    (hφη : ∀ a : S, φ ⟨η a, hη a a.property⟩ = H (φ a))
    (x z v : StarSeries p hp δ η hc)
    (hx : CoefficientsIn S (toSeries x)) (hz : CoefficientsIn S (toSeries z))
    (hv : CoefficientsIn S (toSeries v)) (f : FreeAlgebra k Bool) (n : ℕ) :
    specialize φ (toSeries (Variations.variation f x z v n))
        (DifferentialCoefficients.variation p hp δ η hc hδ hη x z v hx hz hv f n) =
      toSeries (Variations.variation f
        (ofSeries (hp := hp) (h := hDH) (specialize φ (toSeries x) hx))
        (ofSeries (specialize φ (toSeries z) hz))
        (ofSeries (specialize φ (toSeries v) hv)) n) := by
  let A := starSubalgebra p hp δ η hc hδ hη
  let x' : A := ⟨x, hx⟩
  let z' : A := ⟨z, hz⟩
  let v' : A := ⟨v, hv⟩
  have heq : Variations.variation f x' z' v' n =
      (⟨Variations.variation f x z v n,
        DifferentialCoefficients.variation p hp δ η hc hδ hη x z v hx hz hv f n⟩ : A) := by
    apply Subtype.ext
    exact Variations.map_variation A.val f x' z' v' n
  have hm := Variations.map_variation
    (specializeAlgHom φ p hp δ η D H hc hDH hδ hη hφδ hφη) f x' z' v' n
  rw [heq] at hm
  exact congrArg toSeries hm

end CoefficientAlgebra

section GenericVariation

open GenericJets JetPolynomialCoefficients JetSpecialization

variable {k F E G : Type*} [Field k] [Field F] [Field E] [Field G]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [Algebra k G] [Algebra F G] [IsScalarTower k F G]

omit [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] in
/-- A base-field symbol has polynomial coefficients after extending to the generic jet field. -/
theorem mapField_coefficients (z : LaurentSeries F) :
    CoefficientsIn (polynomialRange (k := k) (F := F))
      (mapField (IsScalarTower.toAlgHom k F E) z) := fun n ↦ base_mem (z.coeff n)

/-- Evaluating generic jets leaves the embedded base symbol unchanged. -/
theorem specialize_mapField (D H : Derivation k G G) (w : G) (z : LaurentSeries F) :
    specialize (evaluation (E := E) D H w)
        (mapField (IsScalarTower.toAlgHom k F E) z) (mapField_coefficients z) =
      mapField (IsScalarTower.toAlgHom k F G) z := by
  ext n
  exact evaluation_base D H w (z.coeff n)

variable [CharZero E] [CharZero G]

/-- The actual variation around a base symbol with a generic monomial perturbation. -/
def genericVariation (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) : LaurentSeries E :=
  SymbolVariations.variation (hp := hp) (h := GenericJets.commute δ η hc) f
    (mapField (IsScalarTower.toAlgHom k F E) z)
    (HahnSeries.single q (jet (F := F) (E := E) 0 0)) j

theorem genericVariation_coefficients (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) :
    CoefficientsIn (polynomialRange (k := k) (F := F))
      (genericVariation (E := E) δ η hc p hp q z f j) := by
  intro n
  exact (mem_polynomialRange (k := k) (F := F) _).mpr
    (variation_coeff_polynomial (E := E) δ η hc p hp q z f j n)

/-- Each generic variation specializes to the variation at the actual mixed-jet element. -/
theorem specialize_genericVariation (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) (j : ℕ) :
    specialize (evaluation (E := E) D H w)
        (genericVariation δ η hc p hp q z f j)
        (genericVariation_coefficients δ η hc p hp q z f j) =
      SymbolVariations.variation (hp := hp) (h := hDH) f
        (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j := by
  have hx : CoefficientsIn (polynomialRange (k := k) (F := F) (E := E))
      (distinguishedSymbol p) :=
    DifferentialCoefficients.single _ (polynomialRange (k := k) (F := F)).one_mem
  have hv : CoefficientsIn (polynomialRange (k := k) (F := F) (E := E))
      (HahnSeries.single q (jet (F := F) 0 0)) :=
    DifferentialCoefficients.single _ (jet_mem 0 0)
  have hh := specialize_variation (evaluation (E := E) D H w) p hp
    (GenericJets.delta δ) (GenericJets.eta η) D H (GenericJets.commute δ η hc) hDH
    (delta_stable δ) (eta_stable η) (evaluation_delta δ D H w hD)
    (evaluation_eta η D H w hDH hH) (ofSeries (distinguishedSymbol p))
    (ofSeries (mapField (IsScalarTower.toAlgHom k F E) z))
    (ofSeries (HahnSeries.single q (jet (F := F) 0 0))) hx
    (mapField_coefficients z) hv f j
  have hxs : specialize (evaluation (E := E) D H w) (distinguishedSymbol p) hx =
      distinguishedSymbol p := by
    simpa [distinguishedSymbol] using
      specialize_single (evaluation (F := F) (E := E) D H w) (-(p : ℤ)) (1 :
        polynomialRange (k := k) (F := F) (E := E))
  have hvs : specialize (evaluation (E := E) D H w)
      (HahnSeries.single q (jet (F := F) 0 0)) hv = HahnSeries.single q w := by
    simpa [evaluation_jet] using specialize_single (evaluation (E := E) D H w) q
      (⟨jet (F := F) 0 0, jet_mem 0 0⟩ : polynomialRange (k := k) (F := F) (E := E))
  simpa only [toSeries_ofSeries, hxs, hvs, specialize_mapField,
    genericVariation, SymbolVariations.variation] using hh

/-- One jet polynomial represents a variation coefficient before and after every specialization. -/
theorem exists_universal_variation_coefficient (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericVariation (E := E) δ η hc p hp q z f j).coeff n ∧
      ∀ (D H : Derivation k G G) (hDH : Function.Commute D H),
        (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) →
        (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) → ∀ w : G,
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
          (SymbolVariations.variation (hp := hp) (h := hDH) f
            (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j).coeff n := by
  obtain ⟨P, hP⟩ := variation_coeff_polynomial (E := E) δ η hc p hp q z f j n
  refine ⟨P, hP, ?_⟩
  intro D H hDH hD hH w
  have hh := congrArg (fun U : LaurentSeries G ↦ U.coeff n)
    (specialize_genericVariation (E := E) δ η hc p hp q z D H hDH hD hH w f j)
  dsimp only at hh
  rw [specialize_coeff] at hh
  have heq : (⟨(genericVariation (E := E) δ η hc p hp q z f j).coeff n,
      genericVariation_coefficients δ η hc p hp q z f j n⟩ :
      polynomialRange (k := k) (F := F)) =
      ⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E P, ⟨P, rfl⟩⟩ := Subtype.ext hP.symm
  rw [heq, evaluation_embed] at hh
  exact hh

end GenericVariation

end

end MakarLimanov.VariationCoefficients
