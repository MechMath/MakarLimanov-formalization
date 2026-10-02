import MakarLimanov.CKStrip

/-!
# A differential indeterminate for two commuting derivations

The coefficient field is the fraction field of the polynomial ring in all mixed jets.
Commutation and algebraic independence are proved for these concrete constructions.
-/

namespace MakarLimanov.GenericJets

open CKStrip

noncomputable section

variable {k F E : Type*} [CommRing k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- The algebraically independent variable with mixed derivative index `(i,j)`. -/
def jet (i j : ℕ) : E :=
  algebraMap (MvPolynomial (ℕ × ℕ) F) E (MvPolynomial.X (i, j))

/-- The first derivation shifts the first jet index and extends the coefficient derivation. -/
def delta (δ : Derivation k F F) : Derivation k E E :=
  rationalDerivation ((Algebra.linearMap F E).compDer δ)
    (fun ij : ℕ × ℕ ↦ jet (F := F) (ij.1 + 1) ij.2)

/-- The second derivation shifts the second jet index and extends the coefficient derivation. -/
def eta (η : Derivation k F F) : Derivation k E E :=
  rationalDerivation ((Algebra.linearMap F E).compDer η)
    (fun ij : ℕ × ℕ ↦ jet (F := F) ij.1 (ij.2 + 1))

@[simp] theorem delta_base (δ : Derivation k F F) (a : F) :
    delta (E := E) δ (algebraMap F E a) = algebraMap F E (δ a) := by
  simp [delta, rationalDerivation_C, LinearMap.compDer]

@[simp] theorem eta_base (η : Derivation k F F) (a : F) :
    eta (E := E) η (algebraMap F E a) = algebraMap F E (η a) := by
  simp [eta, rationalDerivation_C, LinearMap.compDer]

@[simp] theorem delta_jet (δ : Derivation k F F) (i j : ℕ) :
    delta (E := E) δ (jet (F := F) i j) = jet (F := F) (i + 1) j := by
  simp [delta, jet, rationalDerivation_X]

@[simp] theorem eta_jet (η : Derivation k F F) (i j : ℕ) :
    eta (E := E) η (jet (F := F) i j) = jet (F := F) i (j + 1) := by
  simp [eta, jet, rationalDerivation_X]

/-- Commutation on coefficients and generators extends to the whole rational function field. -/
theorem commute (δ η₀ : Derivation k F F) (hc : Function.Commute δ η₀) :
    Function.Commute (delta (E := E) δ) (eta (E := E) η₀) := by
  have hz : ⁅delta (E := E) δ, eta (E := E) η₀⁆ = 0 := by
    apply derivation_ext_rational (F := F) (σ := ℕ × ℕ)
    · intro a
      simp [Derivation.commutator_apply, hc a]
    · rintro ⟨i,j⟩
      change delta (E := E) δ (eta (E := E) η₀ (jet (F := F) i j)) -
        eta (E := E) η₀ (delta (E := E) δ (jet (F := F) i j)) = 0
      simp
  intro a
  simpa [Derivation.commutator_apply, sub_eq_zero] using DFunLike.congr_fun hz a

theorem delta_iterate_jet (δ : Derivation k F F) (i j n : ℕ) :
    (delta (E := E) δ)^[n] (jet (F := F) i j) = jet (F := F) (i + n) j := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih, Nat.add_assoc]

theorem eta_iterate_jet (η : Derivation k F F) (i j n : ℕ) :
    (eta (E := E) η)^[n] (jet (F := F) i j) = jet (F := F) i (j + n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih, Nat.add_assoc]

/-- Every formal jet is the corresponding mixed derivative of one element. -/
theorem mixed_jet (δ η₀ : Derivation k F F) (i j : ℕ) :
    (delta (E := E) δ)^[i] ((eta (E := E) η₀)^[j] (jet (F := F) 0 0)) =
      jet (F := F) i j := by
  simp [eta_iterate_jet, delta_iterate_jet]

/-- Evaluation at all mixed derivatives is precisely the injective fraction-field embedding. -/
theorem eval_mixed (δ η₀ : Derivation k F F) (P : MvPolynomial (ℕ × ℕ) F) :
    MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
      (delta (E := E) δ)^[ij.1] ((eta (E := E) η₀)^[ij.2] (jet (F := F) 0 0))) P =
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P := by
  simp only [mixed_jet]
  have hh : MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ jet (F := F) (E := E) ij.1 ij.2) =
      IsScalarTower.toAlgHom F (MvPolynomial (ℕ × ℕ) F) E := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp [jet]
  exact DFunLike.congr_fun hh P

/-- No nonzero differential polynomial vanishes at the constructed generic element. -/
theorem eval_mixed_ne_zero (δ η₀ : Derivation k F F)
    (P : MvPolynomial (ℕ × ℕ) F) (hP : P ≠ 0) :
    MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
      (delta (E := E) δ)^[ij.1] ((eta (E := E) η₀)^[ij.2] (jet (F := F) 0 0))) P ≠ 0 := by
  rw [eval_mixed]
  simpa only [map_zero] using
    (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E).ne hP

/-- The concrete fraction field supplies a differential indeterminate over any coefficient field. -/
theorem exists_generic (δ η₀ : Derivation k F F) (hc : Function.Commute δ η₀) :
    let E := FractionRing (MvPolynomial (ℕ × ℕ) F)
    ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η₀ a)) ∧
      (∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] v)) P ≠ 0) := by
  exact ⟨delta δ, eta η₀, jet 0 0, commute δ η₀ hc, delta_base δ, eta_base η₀,
    eval_mixed_ne_zero δ η₀⟩

end

end MakarLimanov.GenericJets
