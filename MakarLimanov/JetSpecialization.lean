import MakarLimanov.JetPolynomialCoefficients
import MakarLimanov.SymbolSpecialization

/-! Specialization of polynomial jet coefficients to actual mixed derivatives. -/

namespace MakarLimanov.JetSpecialization

open GenericJets JetPolynomialCoefficients

noncomputable section

variable {k F E G : Type*} [Field k] [Field F] [Field E] [Field G]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [Algebra k G] [Algebra F G] [IsScalarTower k F G]

/-- The polynomial ring is isomorphic to its image, without making that image a field. -/
def rangeEquiv : MvPolynomial (ℕ × ℕ) F ≃ₐ[k] polynomialRange (k := k) (F := F) (E := E) :=
  AlgEquiv.ofInjective (IsScalarTower.toAlgHom k (MvPolynomial (ℕ × ℕ) F) E)
    (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)

/-- Evaluate polynomial coefficients at mixed derivatives; no rational denominator is evaluated. -/
def evaluation (D H : Derivation k G G) (w : G) :
    polynomialRange (k := k) (F := F) (E := E) →ₐ[k] G :=
  ((MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))).restrictScalars k).comp
    rangeEquiv.symm.toAlgHom

omit [Algebra F E] [IsScalarTower k F E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E] in
@[simp] theorem evaluation_embed (D H : Derivation k G G) (w : G)
    (P : MvPolynomial (ℕ × ℕ) F) :
    evaluation (E := E) D H w ⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E P, ⟨P, rfl⟩⟩ =
      MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P := by
  change ((MvPolynomial.aeval _).restrictScalars k)
    (rangeEquiv.symm (rangeEquiv P)) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

omit [IsScalarTower k F E] in
theorem evaluation_base (D H : Derivation k G G) (w : G) (a : F) :
    evaluation (E := E) D H w ⟨algebraMap F E a, base_mem a⟩ = algebraMap F G a := by
  have he := evaluation_embed (E := E) D H w (MvPolynomial.C a)
  have hh : algebraMap (MvPolynomial (ℕ × ℕ) F) E (MvPolynomial.C a) = algebraMap F E a :=
    (IsScalarTower.algebraMap_apply F (MvPolynomial (ℕ × ℕ) F) E a).symm
  simpa only [hh, MvPolynomial.aeval_C] using he

omit [Algebra F E] [IsScalarTower k F E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E] in
theorem evaluation_jet (D H : Derivation k G G) (w : G) (i j : ℕ) :
    evaluation (E := E) D H w ⟨jet (F := F) i j, jet_mem i j⟩ = D^[i] (H^[j] w) := by
  simpa only [MvPolynomial.aeval_X] using evaluation_embed (E := E) D H w (MvPolynomial.X (i,j))

omit [Algebra F G] [IsScalarTower k F G] [IsScalarTower k F E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] in
/-- Compatibility on coefficients and variables extends to every polynomial coefficient. -/
theorem differential_compat (φ : polynomialRange (k := k) (F := F) (E := E) →ₐ[k] G)
    (d : Derivation k E E) (d' : Derivation k G G)
    (hd : ∀ a ∈ polynomialRange (k := k) (F := F), d a ∈ polynomialRange (k := k) (F := F))
    (hC : ∀ a : F, φ ⟨d (algebraMap F E a), hd _ (base_mem a)⟩ =
      d' (φ ⟨algebraMap F E a, base_mem a⟩))
    (hX : ∀ i j, φ ⟨d (jet (F := F) i j), hd _ (jet_mem i j)⟩ =
      d' (φ ⟨jet (F := F) i j, jet_mem i j⟩)) :
    ∀ a : polynomialRange (k := k) (F := F), φ ⟨d a, hd a a.property⟩ = d' (φ a) := by
  rintro ⟨a, P, rfl⟩
  change φ ⟨d (algebraMap (MvPolynomial (ℕ × ℕ) F) E P), _⟩ =
    d' (φ ⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E P, _⟩)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hh : algebraMap (MvPolynomial (ℕ × ℕ) F) E (MvPolynomial.C a) = algebraMap F E a :=
      (IsScalarTower.algebraMap_apply F (MvPolynomial (ℕ × ℕ) F) E a).symm
    simpa only [hh] using hC a
  | add P Q hP hQ =>
    let u : polynomialRange (k := k) (F := F) (E := E) := ⟨_, ⟨P, rfl⟩⟩
    let v : polynomialRange (k := k) (F := F) (E := E) := ⟨_, ⟨Q, rfl⟩⟩
    have he : (⟨d (algebraMap (MvPolynomial (ℕ × ℕ) F) E (P + Q)),
        hd _ ⟨P + Q, rfl⟩⟩ : polynomialRange (k := k) (F := F)) =
        ⟨d u, hd u u.property⟩ + ⟨d v, hd v v.property⟩ := by
      apply Subtype.ext
      simp [u, v]
    rw [he, map_add]
    have hu : φ ⟨d u, hd u u.property⟩ = d' (φ u) := hP
    have hv : φ ⟨d v, hd v v.property⟩ = d' (φ v) := hQ
    rw [hu, hv]
    have huv : (⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E (P + Q),
        ⟨P + Q, rfl⟩⟩ : polynomialRange (k := k) (F := F)) = u + v := by
      apply Subtype.ext
      exact map_add _ _ _
    rw [huv]
    rw [map_add, map_add]
  | mul_X P ij hP =>
    let u : polynomialRange (k := k) (F := F) (E := E) := ⟨_, ⟨P, rfl⟩⟩
    let v : polynomialRange (k := k) (F := F) (E := E) := ⟨jet ij.1 ij.2, jet_mem _ _⟩
    have he : (⟨d (algebraMap (MvPolynomial (ℕ × ℕ) F) E (P * MvPolynomial.X ij)),
        hd _ ⟨P * MvPolynomial.X ij, rfl⟩⟩ : polynomialRange (k := k) (F := F)) =
        u * ⟨d v, hd v v.property⟩ + v * ⟨d u, hd u u.property⟩ := by
      apply Subtype.ext
      simp [u, v, jet, Derivation.leibniz, smul_eq_mul]
    rw [he, map_add, map_mul, map_mul]
    have hu : φ ⟨d u, hd u u.property⟩ = d' (φ u) := hP
    have hv : φ ⟨d v, hd v v.property⟩ = d' (φ v) := hX ij.1 ij.2
    rw [hu, hv]
    have huv : (⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E (P * MvPolynomial.X ij),
        ⟨P * MvPolynomial.X ij, rfl⟩⟩ : polynomialRange (k := k) (F := F)) = u * v := by
      apply Subtype.ext
      exact map_mul _ _ _
    rw [huv]
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem evaluation_delta (δ : Derivation k F F) (D H : Derivation k G G) (w : G)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) :
    ∀ a : polynomialRange (k := k) (F := F) (E := E),
      evaluation D H w ⟨GenericJets.delta (E := E) δ a, delta_stable δ (a : E) a.property⟩ =
        D (evaluation D H w a) := by
  apply differential_compat
  · intro a
    simp only [delta_base, evaluation_base, hD]
  · intro i j
    simp only [delta_jet, evaluation_jet, Function.iterate_succ_apply']

theorem evaluation_eta (η : Derivation k F F) (D H : Derivation k G G) (w : G)
    (hc : Function.Commute D H)
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) :
    ∀ a : polynomialRange (k := k) (F := F) (E := E),
      evaluation D H w ⟨GenericJets.eta (E := E) η a, eta_stable η (a : E) a.property⟩ =
        H (evaluation D H w a) := by
  apply differential_compat
  · intro a
    simp only [eta_base, evaluation_base, hH]
  · intro i j
    simp only [eta_jet, evaluation_jet, Function.iterate_succ_apply']
    exact hc.iterate_left i (H^[j] w)

variable [CharZero E] [CharZero G]

open SymbolSeries SymbolSeries.StarSeries DifferentialCoefficients SymbolSpecialization

/-- The actual generic-symbol substitution, with its polynomial coefficient certificate. -/
def genericInput (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) :
    Bool → StarSeries p hp (GenericJets.delta (E := E) δ) (GenericJets.eta η)
      (GenericJets.commute δ η hc) :=
  fun b ↦ ofSeries (if b then HahnSeries.single q (jet (F := F) 0 0)
    else distinguishedSymbol p)

omit [CharZero E] in
theorem genericInput_coefficients (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (b : Bool) :
    CoefficientsIn (polynomialRange (k := k) (F := F))
      (toSeries (genericInput (E := E) δ η hc p hp q b)) := by
  cases b
  · exact DifferentialCoefficients.single _ (polynomialRange (k := k) (F := F)).one_mem
  · exact DifferentialCoefficients.single _ (jet_mem 0 0)

omit [CharZero E] [CharZero G] in
theorem specialize_genericInput (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (D H : Derivation k G G) (w : G) (b : Bool) :
    specialize (evaluation (E := E) D H w)
        (toSeries (genericInput δ η hc p hp q b))
        (genericInput_coefficients δ η hc p hp q b) =
      if b then HahnSeries.single q w else distinguishedSymbol p := by
  cases b
  · have hh := specialize_single (evaluation (F := F) (E := E) D H w) (-(p : ℤ)) 1
    simpa [genericInput, distinguishedSymbol] using hh
  · have hh := specialize_single (evaluation (E := E) D H w) q
      (⟨jet (F := F) 0 0, jet_mem 0 0⟩ : polynomialRange (k := k) (F := F) (E := E))
    simpa [genericInput, evaluation_jet] using hh

/-- Substituting any compatible differential element specializes the genuine generic symbol. -/
theorem specialize_evaluateAt (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) :
    specialize (evaluation (E := E) D H w)
        (toSeries (FreeAlgebra.lift k (genericInput δ η hc p hp q) f))
        (DifferentialCoefficients.evaluate p hp _ _ (GenericJets.commute δ η hc)
          (delta_stable δ) (eta_stable η) _ (genericInput_coefficients δ η hc p hp q) f) =
      toSeries (evaluateAt (hp := hp) (h := hDH) (HahnSeries.single q w) f) := by
  rw [specialize_evaluate (evaluation D H w) p hp _ _ D H
    (GenericJets.commute δ η hc) hDH (delta_stable δ) (eta_stable η)
    (evaluation_delta δ D H w hD) (evaluation_eta η D H w hDH hH)
    _ (genericInput_coefficients δ η hc p hp q)]
  simp only [specialize_genericInput]
  rfl

/-- A concrete nonzero symbol value proves nonvanishing of the generic symbol. -/
theorem generic_ne_zero_of_value (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool)
    (hf : toSeries (evaluateAt (hp := hp) (h := hDH) (HahnSeries.single q w) f) ≠ 0) :
    toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) (E := E) 0 0)) f) ≠ 0 := by
  intro hz
  apply hf
  rw [← specialize_evaluateAt (E := E) δ η hc p hp q D H hDH hD hH w f]
  change specialize (evaluation D H w)
    (toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) (E := E) 0 0)) f)) _ = 0
  simp only [hz, specialize_zero]

/-- Specialization cannot create a coefficient below a generic lower support bound. -/
theorem value_lowerBound (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) (b : ℤ)
    (hb : LowerBound b (toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) (E := E) 0 0)) f))) :
    LowerBound b (toSeries (evaluateAt (hp := hp) (h := hDH) (HahnSeries.single q w) f)) := by
  rw [← specialize_evaluateAt (E := E) δ η hc p hp q D H hDH hD hH w f]
  exact SymbolSpecialization.lowerBound _ _ _ hb

/-- One fixed polynomial represents a coefficient at every compatible differential specialization. -/
theorem exists_universal_coefficient (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (f : FreeAlgebra k Bool) (n : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
          (HahnSeries.single q (jet (F := F) (E := E) 0 0)) f)).coeff n ∧
      ∀ (D H : Derivation k G G) (hDH : Function.Commute D H),
        (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) →
        (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) → ∀ w : G,
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
          (toSeries (evaluateAt (hp := hp) (h := hDH) (HahnSeries.single q w) f)).coeff n := by
  obtain ⟨P, hP⟩ := evaluateAt_coeff_polynomial (E := E) δ η hc p hp q f n
  refine ⟨P, hP, ?_⟩
  intro D H hDH hD hH w
  have hh := congrArg (fun z : LaurentSeries G ↦ z.coeff n)
    (specialize_evaluateAt (E := E) δ η hc p hp q D H hDH hD hH w f)
  dsimp only at hh
  rw [specialize_coeff] at hh
  have hh' : (⟨(toSeries (FreeAlgebra.lift k (genericInput (E := E) δ η hc p hp q) f)).coeff n,
      DifferentialCoefficients.evaluate p hp _ _ (GenericJets.commute δ η hc)
        (delta_stable δ) (eta_stable η) _ (genericInput_coefficients δ η hc p hp q) f n⟩ :
      polynomialRange (k := k) (F := F)) =
      ⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E P, ⟨P, rfl⟩⟩ := by
    apply Subtype.ext
    exact hP.symm
  rw [hh', evaluation_embed] at hh
  exact hh

omit [Algebra F E] [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E] [CharZero E] in
/-- The representing polynomial is unique because the generic coefficient embedding is injective. -/
theorem coefficient_representative_unique (a : E) (P Q : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P = a)
    (hQ : algebraMap (MvPolynomial (ℕ × ℕ) F) E Q = a) : P = Q :=
  IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E (hP.trans hQ.symm)

end

end MakarLimanov.JetSpecialization
