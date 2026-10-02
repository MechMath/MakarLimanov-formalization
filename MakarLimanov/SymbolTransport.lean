import MakarLimanov.SymbolReindex

/-!
# Simultaneous differential field extension and lattice refinement

Newton steps may enlarge the coefficient field and the exponent lattice at once. The map below
acts on actual Laurent symbols; it preserves star multiplication, polynomial evaluation, and
all variations. Finite support and the two bounds used by finite approximations are transported
with the correct denominator factors.
-/

noncomputable section

namespace MakarLimanov.SymbolSeries

open HahnSeries StarSeries

variable {k F G : Type*} [Field k] [Field F] [Field G] [Algebra k F] [Algebra k G]

/-- An injective coefficient-field extension preserves the support exactly. -/
theorem support_mapField (φ : F →ₐ[k] G) (x : LaurentSeries F) :
    (mapField φ x).support = x.support := by
  ext n
  simp only [mem_support, mapField_coeff, map_ne_zero]

/-- Field extension does not change the least support index. -/
theorem order_mapField (φ : F →ₐ[k] G) (x : LaurentSeries F) :
    (mapField φ x).order = x.order := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : mapField φ x ≠ 0 := by
    intro hz
    apply hx
    apply mapField_injective φ
    simpa using hz
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    simpa using (HahnSeries.coeff_order_eq_zero.not.mpr hx)
  · apply (HahnSeries.le_order_iff_forall hx').mpr
    exact (lowerBound_mapField_iff φ x.order x).mpr (lowerBound_order x)

@[simp] theorem mapField_distinguished (φ : F →ₐ[k] G) (p : ℕ) :
    mapField φ (distinguishedSymbol p) = distinguishedSymbol p := by
  simp [distinguishedSymbol]

section FieldEvaluation

variable [CharZero F] [CharZero G]

/-- A differential field extension commutes with ordered free-polynomial evaluation. -/
theorem mapField_evaluatePair (φ : F →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (x y : LaurentSeries F) (f : FreeAlgebra k Bool) :
    mapField φ (toSeries (evaluatePair (hp := hp) (h := h) x y f)) =
      toSeries (evaluatePair (hp := hp) (h := h') (mapField φ x) (mapField φ y) f) := by
  have hh : (mapFieldAlgHom φ p hp δ η δ' η' h h' hδ hη).comp
      (evaluatePair (hp := hp) (h := h) x y) =
      evaluatePair (hp := hp) (h := h') (mapField φ x) (mapField φ y) := by
    apply FreeAlgebra.hom_ext
    funext b
    cases b <;> simp [evaluatePair, evaluate, mapFieldAlgHom]
  exact congrArg toSeries (DFunLike.congr_fun hh f)

/-- Extending the differential field transports the actual Newton residual. -/
theorem mapField_evaluateAt (φ : F →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) :
    mapField φ (toSeries (evaluateAt (hp := hp) (h := h) z f)) =
      toSeries (evaluateAt (hp := hp) (h := h') (mapField φ z) f) := by
  simpa only [evaluateAt, mapField_distinguished] using
    mapField_evaluatePair φ p hp δ η δ' η' h h' hδ hη (distinguishedSymbol p) z f

/-- Field extensions preserve each coefficient of the central variation expansion. -/
theorem mapField_variation (φ : F →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℕ) :
    mapField φ (SymbolVariations.variation (hp := hp) (h := h) f z v n) =
      SymbolVariations.variation (hp := hp) (h := h') f (mapField φ z) (mapField φ v) n := by
  have heq := Variations.map_variation (mapFieldAlgHom φ p hp δ η δ' η' h h' hδ hη) f
    (ofSeries (distinguishedSymbol p)) (ofSeries z) (ofSeries v) n
  have hD : mapFieldAlgHom φ p hp δ η δ' η' h h' hδ hη
      (ofSeries (distinguishedSymbol p)) = ofSeries (distinguishedSymbol p) := by
    change mapField φ (distinguishedSymbol p) = distinguishedSymbol p
    exact mapField_distinguished φ p
  rw [hD] at heq
  exact congrArg toSeries heq

end FieldEvaluation

/-- Enlarge the differential coefficient field and multiply all indices by the new lattice factor. -/
def transportSymbol (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) : LaurentSeries G :=
  refineLattice e he (mapField φ x)

@[simp] theorem transportSymbol_coeff (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) (n : ℤ) :
    (transportSymbol φ e he x).coeff ((e : ℤ) * n) = φ (x.coeff n) := by
  simp [transportSymbol]

/-- Transport sends the original support onto its multiplied support. -/
theorem support_transportSymbol (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) :
    (transportSymbol φ e he x).support = (fun n : ℤ ↦ (e : ℤ) * n) '' x.support := by
  rw [transportSymbol, support_refineLattice, support_mapField]

/-- Transport preserves finite support. -/
theorem finite_support_transportSymbol (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) (hx : x.support.Finite) :
    (transportSymbol φ e he x).support.Finite := by
  rw [support_transportSymbol]
  exact hx.image _

/-- The old order is scaled solely by the lattice factor. -/
theorem order_transportSymbol (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) :
    (transportSymbol φ e he x).order = (e : ℤ) * x.order := by
  rw [transportSymbol, order_refineLattice, order_mapField]

/-- The leading coefficient embeds in the enlarged field without further factors. -/
theorem coeff_order_transportSymbol (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) :
    (transportSymbol φ e he x).coeff (transportSymbol φ e he x).order =
      φ (x.coeff x.order) := by
  rw [order_transportSymbol, transportSymbol_coeff]

theorem lowerBound_transportSymbol_iff (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) (b : ℤ) :
    LowerBound ((e : ℤ) * b) (transportSymbol φ e he x) ↔ LowerBound b x := by
  rw [transportSymbol, lowerBound_refineLattice_iff, lowerBound_mapField_iff]

/-- The combined transport is the composition of the actual star-algebra embeddings. -/
def transportSymbolAlgHom [CharZero F] [CharZero G]
    (φ : F →ₐ[k] G) (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a)) :
    StarSeries p hp δ η h →ₐ[k] StarSeries (p * e) (Nat.mul_pos hp he) δ' η' h' :=
  (refineLatticeAlgHom p e hp he δ' η' h').comp
    (mapFieldAlgHom φ p hp δ η δ' η' h h' hδ hη)

section TransportEvaluation

variable [CharZero F] [CharZero G]

/-- The residual computed in the new symbol algebra is exactly the transported old residual. -/
theorem transportSymbol_evaluateAt (φ : F →ₐ[k] G) (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) :
    transportSymbol φ e he (toSeries (evaluateAt (hp := hp) (h := h) z f)) =
      toSeries (evaluateAt (hp := Nat.mul_pos hp he) (h := h')
        (transportSymbol φ e he z) f) := by
  rw [transportSymbol, mapField_evaluateAt φ p hp δ η δ' η' h h' hδ hη,
    refineLattice_evaluateAt]
  rfl

/-- Every Newton variation commutes with simultaneous coefficient and lattice transport. -/
theorem transportSymbol_variation (φ : F →ₐ[k] G) (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℕ) :
    transportSymbol φ e he (SymbolVariations.variation (hp := hp) (h := h) f z v n) =
      SymbolVariations.variation (hp := Nat.mul_pos hp he) (h := h') f
        (transportSymbol φ e he z) (transportSymbol φ e he v) n := by
  rw [transportSymbol, mapField_variation φ p hp δ η δ' η' h h' hδ hη,
    refineLattice_variation]
  rfl

/-- The complete finite-support and two-bound invariant survives simultaneous transport. -/
theorem transportSymbol_approximation_bounds (φ : F →ₐ[k] G) (p e : ℕ)
    (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (A T : ℕ)
    (hz : z.support.Finite) (hb : LowerBound (-((p : ℤ) * A)) z)
    (hr : LowerBound ((p : ℤ) * T) (toSeries (evaluateAt (hp := hp) (h := h) z f))) :
    (transportSymbol φ e he z).support.Finite ∧
      LowerBound (-(((p * e : ℕ) : ℤ) * A)) (transportSymbol φ e he z) ∧
      LowerBound (((p * e : ℕ) : ℤ) * T)
        (toSeries (evaluateAt (hp := Nat.mul_pos hp he) (h := h')
          (transportSymbol φ e he z) f)) := by
  refine ⟨finite_support_transportSymbol φ e he z hz, ?_, ?_⟩
  · convert (lowerBound_transportSymbol_iff φ e he z (-((p : ℤ) * A))).mpr hb using 1
    push_cast
    ring
  · rw [← transportSymbol_evaluateAt φ p e hp he δ η δ' η' h h' hδ hη]
    convert (lowerBound_transportSymbol_iff φ e he _ ((p : ℤ) * T)).mpr hr using 1
    push_cast
    ring

end TransportEvaluation

/-- A single Newton correction preserves finite support after the combined transport. -/
theorem finite_support_transportSymbol_add_single (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (z : LaurentSeries F) (hz : z.support.Finite) (q : ℤ) (a : G) :
    (transportSymbol φ e he z + single q a).support.Finite := by
  apply finite_support_refineLattice_add_single e he (mapField φ z)
  simpa only [support_mapField] using hz

/-- Corrections above the uniform pole bound preserve that bound across both extensions. -/
theorem lowerBound_transportSymbol_add_single (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (z : LaurentSeries F) (b q : ℤ) (a : G)
    (hb : LowerBound b z) (hq : (e : ℤ) * b ≤ q) :
    LowerBound ((e : ℤ) * b) (transportSymbol φ e he z + single q a) := by
  apply lowerBound_refineLattice_add_single e he (mapField φ z) b q a
  · exact (lowerBound_mapField_iff φ b z).mpr hb
  · exact hq

end MakarLimanov.SymbolSeries
