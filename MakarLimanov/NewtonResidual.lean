import MakarLimanov.VariationCoefficients
import MakarLimanov.SymbolTransport

/-!
# Cancellation of the actual Newton residual

Every coefficient of the residual after a generic monomial correction is a polynomial in
finitely many mixed jets. Its specialization is the coefficient of the actual corrected
symbol. A root of the leading polynomial therefore improves the Laurent bound by one unit.
-/

noncomputable section

namespace MakarLimanov.NewtonResidual

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open DifferentialCoefficients SymbolSpecialization
open GenericJets JetPolynomialCoefficients JetSpecialization VariationCoefficients

section Bounds

variable {F : Type*} [Field F]

/-- Cancelling the first possible coefficient improves an integer support bound by one. -/
theorem lowerBound_succ_of_coeff_eq_zero (x : LaurentSeries F) (r : ℤ)
    (hx : LowerBound r x) (hr : x.coeff r = 0) : LowerBound (r + 1) x := by
  intro n hn
  by_cases heq : n = r
  · simpa only [heq] using hr
  · exact hx n (by omega)

end Bounds

section GenericResidual

variable {k F E G : Type*} [Field k] [Field F] [Field E] [Field G]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [Algebra k G] [Algebra F G] [IsScalarTower k F G]

/-- Add a HahnSeries.single universal mixed-jet coefficient to a base-field Laurent symbol. -/
def genericCorrectedSymbol (z : LaurentSeries F) (q : ℤ) : LaurentSeries E :=
  mapField (IsScalarTower.toAlgHom k F E) z + HahnSeries.single q (jet (F := F) 0 0)

omit [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] in
theorem genericCorrectedSymbol_coefficients (z : LaurentSeries F) (q : ℤ) :
    CoefficientsIn (polynomialRange (k := k) (F := F))
      (genericCorrectedSymbol (k := k) (E := E) z q) :=
  DifferentialCoefficients.add (mapField_coefficients z)
    (DifferentialCoefficients.single q (jet_mem 0 0))

/-- Evaluation of generic jets sends the universal correction to the actual correction. -/
theorem specialize_genericCorrectedSymbol (D H : Derivation k G G) (w : G)
    (z : LaurentSeries F) (q : ℤ) :
    specialize (evaluation (E := E) D H w)
        (genericCorrectedSymbol (k := k) z q) (genericCorrectedSymbol_coefficients z q) =
      mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w := by
  change specialize (evaluation (E := E) D H w)
    (mapField (IsScalarTower.toAlgHom k F E) z +
      HahnSeries.single q (jet (F := F) 0 0)) _ = _
  rw [specialize_add (evaluation (E := E) D H w) _ _ (mapField_coefficients z)
    (DifferentialCoefficients.single q (jet_mem 0 0)), specialize_mapField]
  have heq := specialize_single (evaluation (E := E) D H w) q
    (⟨jet (F := F) 0 0, jet_mem 0 0⟩ : polynomialRange (k := k) (F := F) (E := E))
  simpa only [evaluation_jet, Function.iterate_zero, id_eq] using
    congrArg (fun v ↦ mapField (IsScalarTower.toAlgHom k F G) z + v) heq

variable [CharZero E] [CharZero G]

/-- The true free-polynomial residual at the generic corrected Laurent symbol. -/
def genericResidual (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) : LaurentSeries E :=
  toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
    (genericCorrectedSymbol (k := k) z q) f)

/-- The full residual, including its unchanged base symbol, has polynomial jet coefficients. -/
theorem genericResidual_coefficients (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F) (f : FreeAlgebra k Bool) :
    CoefficientsIn (polynomialRange (k := k) (F := F))
      (genericResidual (E := E) δ η hc p hp q z f) := by
  apply DifferentialCoefficients.evaluate p hp _ _ (GenericJets.commute δ η hc)
    (delta_stable δ) (eta_stable η)
  intro b
  cases b
  · exact DifferentialCoefficients.single _ (polynomialRange (k := k) (F := F)).one_mem
  · exact genericCorrectedSymbol_coefficients z q

/-- The residual specializes to evaluation at the actual corrected symbol. -/
theorem specialize_genericResidual (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) :
    specialize (evaluation (E := E) D H w)
        (genericResidual δ η hc p hp q z f)
        (genericResidual_coefficients δ η hc p hp q z f) =
      toSeries (evaluateAt (hp := hp) (h := hDH)
        (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f) := by
  let X : Bool → StarSeries p hp (GenericJets.delta (E := E) δ) (GenericJets.eta η)
      (GenericJets.commute δ η hc) :=
    fun b ↦ ofSeries (if b then genericCorrectedSymbol (k := k) z q
      else distinguishedSymbol p)
  have hX : ∀ b, CoefficientsIn (polynomialRange (k := k) (F := F)) (toSeries (X b)) := by
    intro b
    cases b
    · exact DifferentialCoefficients.single _ (polynomialRange (k := k) (F := F)).one_mem
    · exact genericCorrectedSymbol_coefficients z q
  have hh := specialize_evaluate (evaluation (E := E) D H w) p hp _ _ D H
    (GenericJets.commute δ η hc) hDH (delta_stable δ) (eta_stable η)
    (evaluation_delta δ D H w hD) (evaluation_eta η D H w hDH hH) X hX f
  have hi : (fun b ↦ ofSeries (hp := hp) (h := hDH)
      (specialize (evaluation (E := E) D H w) (toSeries (X b)) (hX b))) =
      (fun b ↦ ofSeries (hp := hp) (h := hDH)
        (if b then mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w
          else distinguishedSymbol p)) := by
    funext b
    cases b
    · change ofSeries (specialize (evaluation (E := E) D H w) (HahnSeries.single (-(p : ℤ)) 1) _) = _
      have hsingle := specialize_single (evaluation (E := E) D H w) (-(p : ℤ))
        (1 : polynomialRange (k := k) (F := F) (E := E))
      simpa only [map_one] using congrArg (ofSeries (hp := hp) (h := hDH)) hsingle
    · change ofSeries (specialize (evaluation (E := E) D H w)
        (genericCorrectedSymbol (k := k) z q) _) = _
      exact congrArg (ofSeries (hp := hp) (h := hDH))
        (specialize_genericCorrectedSymbol (E := E) D H w z q)
  rw [hi] at hh
  exact hh

/-- A coefficient has one polynomial representative valid for every compatible specialization. -/
theorem exists_universal_residual_coefficient (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (n : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericResidual (E := E) δ η hc p hp q z f).coeff n ∧
      ∀ (D H : Derivation k G G) (hDH : Function.Commute D H),
        (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) →
        (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) → ∀ w : G,
        MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
          (toSeries (evaluateAt (hp := hp) (h := hDH)
            (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)).coeff n := by
  obtain ⟨P, hP⟩ := (mem_polynomialRange (k := k) (F := F) _).mp
    (genericResidual_coefficients (E := E) δ η hc p hp q z f n)
  refine ⟨P, hP, ?_⟩
  intro D H hDH hD hH w
  have hh := congrArg (fun U : LaurentSeries G ↦ U.coeff n)
    (specialize_genericResidual (E := E) δ η hc p hp q z D H hDH hD hH w f)
  dsimp only at hh
  rw [specialize_coeff] at hh
  have heq : (⟨(genericResidual (E := E) δ η hc p hp q z f).coeff n,
      genericResidual_coefficients δ η hc p hp q z f n⟩ :
      polynomialRange (k := k) (F := F)) =
      ⟨algebraMap (MvPolynomial (ℕ × ℕ) F) E P, ⟨P, rfl⟩⟩ := Subtype.ext hP.symm
  rw [heq, evaluation_embed] at hh
  exact hh

/-- Generic residual bounds descend through a differential root specialization. -/
theorem residual_lowerBound_of_generic (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) (r : ℤ)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f)) :
    LowerBound r (toSeries (evaluateAt (hp := hp) (h := hDH)
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  rw [← specialize_genericResidual (E := E) δ η hc p hp q z D H hDH hD hH w f]
  exact SymbolSpecialization.lowerBound _ _ _ hr

/-- A root of the actual leading coefficient polynomial strictly improves residual precision. -/
theorem residual_improves_of_root (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) (r : ℤ)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hw : MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P = 0) :
    LowerBound (r + 1) (toSeries (evaluateAt (hp := hp) (h := hDH)
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  apply lowerBound_succ_of_coeff_eq_zero _ r
  · exact residual_lowerBound_of_generic δ η hc p hp q z D H hDH hD hH w f r hr
  · obtain ⟨Q, hQ, hvalue⟩ :=
      exists_universal_residual_coefficient (E := E) (G := G) δ η hc p hp q z f r
    have hPQ : P = Q := (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
      (hP.trans hQ.symm)
    rw [← hvalue D H hDH hD hH w, ← hPQ]
    exact hw

/-- Root cancellation supplies a genuine finite corrected symbol with the inherited pole bound. -/
theorem corrected_symbol_of_root (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hw : MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P = 0) :
    (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1) (toSeries (evaluateAt (hp := hp) (h := hDH)
        (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  refine ⟨?_, ?_, residual_improves_of_root δ η hc p hp q z D H hDH hD hH w f r hr P hP hw⟩
  · apply (hz.union ((Set.finite_singleton q).subset
      (HahnSeries.support_single_subset (r := w)))).subset
    simpa only [support_mapField] using HahnSeries.support_add_subset
      (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w)
  · apply ((lowerBound_mapField_iff (IsScalarTower.toAlgHom k F G) b z).mpr hb).add
    intro n hn
    exact HahnSeries.coeff_single_of_ne (by omega)

end GenericResidual

end MakarLimanov.NewtonResidual
