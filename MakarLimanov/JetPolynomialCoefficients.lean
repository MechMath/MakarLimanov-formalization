import MakarLimanov.DifferentialCoefficients
import MakarLimanov.GenericJets

/-! Actual polynomial jet representatives of the coefficients of free-polynomial symbols. -/

namespace MakarLimanov.JetPolynomialCoefficients

open GenericJets DifferentialCoefficients SymbolSeries SymbolSeries.StarSeries

noncomputable section

variable {k F E : Type*} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- Polynomial jet expressions embedded into their fraction field, as a base subalgebra. -/
def polynomialRange : Subalgebra k E :=
  (IsScalarTower.toAlgHom k (MvPolynomial (ℕ × ℕ) F) E).range

omit [Algebra F E] [IsScalarTower k F E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] in
theorem mem_polynomialRange (a : E) : a ∈ polynomialRange (k := k) (F := F) ↔
    ∃ P : MvPolynomial (ℕ × ℕ) F, algebraMap (MvPolynomial (ℕ × ℕ) F) E P = a := Iff.rfl

omit [IsScalarTower k F E] [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] in
theorem base_mem (a : F) : algebraMap F E a ∈ polynomialRange (k := k) (F := F) := by
  refine ⟨MvPolynomial.C a, ?_⟩
  exact (IsScalarTower.algebraMap_apply F (MvPolynomial (ℕ × ℕ) F) E a).symm

omit [Algebra F E] [IsScalarTower k F E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] in
theorem jet_mem (i j : ℕ) : jet (F := F) (E := E) i j ∈ polynomialRange (k := k) (F := F) :=
  ⟨MvPolynomial.X (i,j), rfl⟩

/-- Stability under a derivation follows by polynomial induction on coefficients and variables. -/
theorem stable_of_generators (D : Derivation k E E)
    (hC : ∀ a : F, D (algebraMap F E a) ∈ polynomialRange (k := k) (F := F))
    (hX : ∀ i j, D (jet (F := F) i j) ∈ polynomialRange (k := k) (F := F)) :
    ∀ a ∈ polynomialRange (k := k) (F := F), D a ∈ polynomialRange (k := k) (F := F) := by
  rintro a ⟨P, rfl⟩
  change D (algebraMap (MvPolynomial (ℕ × ℕ) F) E P) ∈ polynomialRange (k := k) (F := F)
  induction P using MvPolynomial.induction_on with
  | C a =>
    change D (algebraMap (MvPolynomial (ℕ × ℕ) F) E
      (algebraMap F (MvPolynomial (ℕ × ℕ) F) a)) ∈ _
    rw [← IsScalarTower.algebraMap_apply]
    exact hC a
  | add P Q hP hQ =>
    simpa only [map_add] using (polynomialRange (k := k) (F := F)).add_mem hP hQ
  | mul_X P ij hP =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul]
    exact (polynomialRange (k := k) (F := F)).add_mem
      ((polynomialRange (k := k) (F := F)).mul_mem ⟨P, rfl⟩ (hX ij.1 ij.2))
      ((polynomialRange (k := k) (F := F)).mul_mem (jet_mem ij.1 ij.2) hP)

theorem delta_stable (δ : Derivation k F F) :
    ∀ a ∈ polynomialRange (k := k) (F := F),
      GenericJets.delta (E := E) δ a ∈ polynomialRange (k := k) (F := F) := by
  apply stable_of_generators
  · intro a
    rw [delta_base]
    exact base_mem _
  · intro i j
    rw [delta_jet]
    exact jet_mem _ _

theorem eta_stable (η : Derivation k F F) :
    ∀ a ∈ polynomialRange (k := k) (F := F),
      GenericJets.eta (E := E) η a ∈ polynomialRange (k := k) (F := F) := by
  apply stable_of_generators
  · intro a
    rw [eta_base]
    exact base_mem _
  · intro i j
    rw [eta_jet]
    exact jet_mem _ _

variable [CharZero E]

/-- Every coefficient of `f(D,v D^(-q/p))` is a polynomial in finitely many mixed jets. -/
theorem evaluateAt_coeff_polynomial (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (f : FreeAlgebra k Bool) (n : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
          (HahnSeries.single q (jet (F := F) (E := E) 0 0)) f)).coeff n := by
  apply (mem_polynomialRange (k := k) (F := F) _).mp
  apply DifferentialCoefficients.evaluate p hp _ _ (GenericJets.commute δ η hc)
    (delta_stable δ) (eta_stable η)
  intro b
  cases b
  · exact DifferentialCoefficients.single _ (polynomialRange (k := k) (F := F)).one_mem
  · exact DifferentialCoefficients.single _ (jet_mem 0 0)

/-- Variations about an arbitrary base-field symbol also have polynomial jet coefficients. -/
theorem variation_coeff_polynomial (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (SymbolVariations.variation (hp := hp) (h := GenericJets.commute δ η hc) f
          (mapField (IsScalarTower.toAlgHom k F E) z)
          (HahnSeries.single q (jet (F := F) (E := E) 0 0)) j).coeff n := by
  apply (mem_polynomialRange (k := k) (F := F) _).mp
  apply DifferentialCoefficients.variation p hp _ _ (GenericJets.commute δ η hc)
    (delta_stable δ) (eta_stable η)
  · exact DifferentialCoefficients.single _ (polynomialRange (k := k) (F := F)).one_mem
  · intro m
    exact base_mem (z.coeff m)
  · exact DifferentialCoefficients.single _ (jet_mem 0 0)

end

end MakarLimanov.JetPolynomialCoefficients
