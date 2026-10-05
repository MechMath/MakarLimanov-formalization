import MakarLimanov.SymbolVariations

/-!
# Reindexing symbols along lattice refinements

The concrete lattice embedding preserves polynomial evaluations and variations. Its support
and lower bounds retain the finite data needed when passing to a finer Newton lattice.
-/

noncomputable section

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.SymbolSeries

open HahnSeries StarSeries

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Refinement transports the support by the injective multiplication of integer indices. -/
theorem support_refineLattice (e : ℕ) (he : 0 < e) (x : LaurentSeries F) :
    (refineLattice e he x).support = (fun n : ℤ ↦ (e : ℤ) * n) '' x.support := by
  apply Set.Subset.antisymm HahnSeries.support_embDomain_subset
  rintro n ⟨m, hm, rfl⟩
  change (refineLattice e he x).coeff ((e : ℤ) * m) ≠ 0
  simpa only [refineLattice_coeff] using ((HahnSeries.mem_support x m).mp hm)

/-- A finite symbol remains finite after refining its exponent lattice. -/
theorem finite_support_refineLattice (e : ℕ) (he : 0 < e) (x : LaurentSeries F)
    (hx : x.support.Finite) : (refineLattice e he x).support.Finite := by
  rw [support_refineLattice]
  exact hx.image _

/-- The lower support index is multiplied by the lattice-refinement factor. -/
theorem order_refineLattice (e : ℕ) (he : 0 < e) (x : LaurentSeries F) :
    (refineLattice e he x).order = (e : ℤ) * x.order := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : refineLattice e he x ≠ 0 := by
    intro hz
    apply hx
    apply refineLattice_injective e he
    simpa using hz
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    simpa using (HahnSeries.coeff_order_eq_zero.not.mpr hx)
  · apply (HahnSeries.le_order_iff_forall hx').mpr
    exact (lowerBound_refineLattice_iff e he x.order x).mpr (lowerBound_order x)

/-- Refinement leaves the leading coefficient unchanged. -/
theorem coeff_order_refineLattice (e : ℕ) (he : 0 < e) (x : LaurentSeries F) :
    (refineLattice e he x).coeff (refineLattice e he x).order = x.coeff x.order := by
  rw [order_refineLattice, refineLattice_coeff]

/-- A Newton correction adds just one support index after lattice refinement. -/
theorem finite_support_refineLattice_add_single (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) (hx : x.support.Finite) (q : ℤ) (a : F) :
    (refineLattice e he x + single q a).support.Finite := by
  apply ((finite_support_refineLattice e he x hx).union
    ((Set.finite_singleton q).subset (HahnSeries.support_single_subset (r := a)))).subset
  exact HahnSeries.support_add_subset _ _

/-- Adding a correction above the inherited lower bound preserves that bound. -/
theorem lowerBound_refineLattice_add_single (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) (b q : ℤ) (a : F)
    (hx : LowerBound b x) (hq : (e : ℤ) * b ≤ q) :
    LowerBound ((e : ℤ) * b) (refineLattice e he x + single q a) := by
  apply ((lowerBound_refineLattice_iff e he b x).mpr hx).add
  intro n hn
  exact HahnSeries.coeff_single_of_ne (by omega)

@[simp] theorem refineLattice_identity (x : LaurentSeries F) :
    refineLattice 1 (by decide) x = x := by
  ext n
  simpa only [Nat.cast_one, one_mul] using refineLattice_coeff 1 (by decide) x n

/-- Successive denominator refinements agree with their product. -/
theorem refineLattice_comp (e d : ℕ) (he : 0 < e) (hd : 0 < d)
    (x : LaurentSeries F) :
    refineLattice d hd (refineLattice e he x) =
      refineLattice (d * e) (Nat.mul_pos hd he) x := by
  ext n
  by_cases hn : ∃ a : ℤ, (d : ℤ) * a = n
  · obtain ⟨a, rfl⟩ := hn
    rw [refineLattice_coeff]
    by_cases ha : ∃ b : ℤ, (e : ℤ) * b = a
    · obtain ⟨b, rfl⟩ := ha
      rw [refineLattice_coeff]
      simpa only [Nat.cast_mul, mul_assoc] using
        (refineLattice_coeff (d * e) (Nat.mul_pos hd he) x b).symm
    · rw [refineLattice_coeff_off e he _ _ ha]
      symm
      apply refineLattice_coeff_off
      rintro ⟨b, hb⟩
      apply ha
      refine ⟨b, ?_⟩
      have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
      apply mul_left_cancel₀ hd'
      simpa only [Nat.cast_mul, mul_assoc] using hb
  · rw [refineLattice_coeff_off d hd _ _ hn]
    symm
    apply refineLattice_coeff_off
    rintro ⟨b, hb⟩
    apply hn
    exact ⟨(e : ℤ) * b, by simpa only [Nat.cast_mul, mul_assoc] using hb⟩

section Evaluation

variable [CharZero F]

/-- Polynomial evaluation commutes with the embedding of star algebras. -/
theorem refineLattice_evaluatePair (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (h : Function.Commute δ η)
    (x y : LaurentSeries F) (f : FreeAlgebra k Bool) :
    refineLattice e he (toSeries (evaluatePair (hp := hp) (h := h) x y f)) =
      toSeries (evaluatePair (hp := Nat.mul_pos hp he) (h := h)
        (refineLattice e he x) (refineLattice e he y) f) := by
  have hh : (refineLatticeAlgHom p e hp he δ η h).comp
      (evaluatePair (hp := hp) (h := h) x y) =
      evaluatePair (hp := Nat.mul_pos hp he) (h := h)
        (refineLattice e he x) (refineLattice e he y) := by
    apply FreeAlgebra.hom_ext
    funext b
    cases b <;> simp [evaluatePair, evaluate, refineLatticeAlgHom]
  exact congrArg toSeries (DFunLike.congr_fun hh f)

/-- Refinement preserves the distinguished symbol in the Newton residual. -/
theorem refineLattice_evaluateAt (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (h : Function.Commute δ η)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) :
    refineLattice e he (toSeries (evaluateAt (hp := hp) (h := h) z f)) =
      toSeries (evaluateAt (hp := Nat.mul_pos hp he) (h := h)
        (refineLattice e he z) f) := by
  simpa only [evaluateAt, refineLattice_distinguished] using
    refineLattice_evaluatePair p e hp he δ η h (distinguishedSymbol p) z f

/-- Every actual variation is transported to the refined lattice. -/
theorem refineLattice_variation (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (h : Function.Commute δ η)
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℕ) :
    refineLattice e he (SymbolVariations.variation (hp := hp) (h := h) f z v n) =
      SymbolVariations.variation (hp := Nat.mul_pos hp he) (h := h) f
        (refineLattice e he z) (refineLattice e he v) n := by
  have heq := Variations.map_variation (refineLatticeAlgHom p e hp he δ η h) f
    (ofSeries (distinguishedSymbol p)) (ofSeries z) (ofSeries v) n
  have hD : refineLatticeAlgHom p e hp he δ η h (ofSeries (distinguishedSymbol p)) =
      ofSeries (distinguishedSymbol (p * e)) := by
    change refineLattice e he (distinguishedSymbol p) = distinguishedSymbol (p * e)
    exact refineLattice_distinguished p e he
  rw [hD] at heq
  exact congrArg toSeries heq

/-- A residual bound scales exactly by the change in denominator. -/
theorem lowerBound_refineLattice_evaluateAt_iff (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (h : Function.Commute δ η)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (b : ℤ) :
    LowerBound ((e : ℤ) * b)
        (toSeries (evaluateAt (hp := Nat.mul_pos hp he) (h := h)
          (refineLattice e he z) f)) ↔
      LowerBound b (toSeries (evaluateAt (hp := hp) (h := h) z f)) := by
  rw [← refineLattice_evaluateAt, lowerBound_refineLattice_iff]

end Evaluation

section FieldExtension

variable {G : Type*} [Field G] [Algebra k G]

/-- Field extension and lattice refinement act on independent parts of a series. -/
theorem mapField_refineLattice (φ : F →ₐ[k] G) (e : ℕ) (he : 0 < e)
    (x : LaurentSeries F) :
    mapField φ (refineLattice e he x) = refineLattice e he (mapField φ x) := by
  ext n
  by_cases hn : ∃ m : ℤ, (e : ℤ) * m = n
  · obtain ⟨m, rfl⟩ := hn
    simp
  · simp [refineLattice_coeff_off e he _ n hn]

end FieldExtension

end MakarLimanov.SymbolSeries
