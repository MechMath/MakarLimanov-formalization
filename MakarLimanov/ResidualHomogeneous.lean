import MakarLimanov.SymbolVariations
import MakarLimanov.VariationHomogeneity

/-!
# Homogeneous pieces of a translated residual

At variation order zero, the variation expansion is the actual evaluation at the
translated symbol.  Combining this with the exact shift identity gives a finite
sum of homogeneous (in the perturbation jets) pieces.
-/

namespace MakarLimanov.ResidualHomogeneous

open HahnSeries SymbolSeries SymbolSeries.StarSeries SymbolVariations
open VariationHomogeneity
open ControlledMatrix

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]
variable {p : ℕ} {hp : 0 < p} {δ η : Derivation k F F}
variable {h : Function.Commute δ η}

theorem evaluateAt_eq_variation_zero
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) :
    toSeries (evaluateAt (hp := hp) (h := h) (z + v) f) =
      SymbolVariations.variation (hp := hp) (h := h) f (z + v) v 0 := by
  unfold SymbolVariations.variation
  rw [Variations.variation_zero]
  rfl

theorem translated_residual_variation_sum
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) :
    toSeries (evaluateAt (hp := hp) (h := h) (z + v) f) =
      ∑ j ∈ (Variations.expansion (ofSeries (hp := hp) (h := h)
        (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := h) z)
        (ofSeries (hp := hp) (h := h) v) f).support,
        SymbolVariations.variation (hp := hp) (h := h) f z v j := by
  rw [evaluateAt_eq_variation_zero]
  simpa only [Nat.choose_zero_right, one_smul] using
    (SymbolVariations.variation_shift f z v 0)

theorem translated_residual_coeff_sum
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℤ) :
    (toSeries (evaluateAt (hp := hp) (h := h) (z + v) f)).coeff n =
      ∑ j ∈ (Variations.expansion (ofSeries (hp := hp) (h := h)
        (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := h) z)
        (ofSeries (hp := hp) (h := h) v) f).support,
        (SymbolVariations.variation (hp := hp) (h := h) f z v j).coeff n := by
  rw [translated_residual_variation_sum]
  simp only [HahnSeries.coeff_sum]

theorem variation_coeff_nsmul
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (r j : ℕ) (n : ℤ) :
    (SymbolVariations.variation (hp := hp) (h := h) f z (r • v) j).coeff n =
      (r : F) ^ j *
        (SymbolVariations.variation (hp := hp) (h := h) f z v j).coeff n := by
  rw [symbolVariation_nsmul]
  rw [HahnSeries.coeff_smul]
  simp [Algebra.smul_def]

theorem exists_nonzero_variation_component
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℤ)
    (hn : (toSeries (evaluateAt (hp := hp) (h := h) (z + v) f)).coeff n ≠ 0) :
    ∃ j ∈ (Variations.expansion (ofSeries (hp := hp) (h := h)
        (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := h) z)
        (ofSeries (hp := hp) (h := h) v) f).support,
      (SymbolVariations.variation (hp := hp) (h := h) f z v j).coeff n ≠ 0 := by
  rw [translated_residual_coeff_sum] at hn
  by_contra! hzero
  apply hn
  exact Finset.sum_eq_zero (fun j hj ↦ hzero j hj)

theorem variation_eq_zero_of_wordDegree_lt
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℕ)
    (hn : ControlledMatrix.wordDegree f < n) :
    SymbolVariations.variation (hp := hp) (h := h) f z v n = 0 := by
  unfold SymbolVariations.variation
  have hzero := Variations.variation_eq_zero_of_count_lt
    f
    (ofSeries (hp := hp) (h := h) (distinguishedSymbol p))
    (ofSeries (hp := hp) (h := h) z) (ofSeries (hp := hp) (h := h) v)
    (ControlledMatrix.wordDegree f) n (by
      intro w hw
      exact (List.count_le_length).trans
        (ControlledMatrix.degreeBound_wordDegree f w hw)) hn
  exact congrArg toSeries hzero

theorem exists_nonzero_variation_component_bounded
    (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℤ)
    (hn : (toSeries (evaluateAt (hp := hp) (h := h) (z + v) f)).coeff n ≠ 0) :
    ∃ j, j ≤ ControlledMatrix.wordDegree f ∧
      (SymbolVariations.variation (hp := hp) (h := h) f z v j).coeff n ≠ 0 := by
  obtain ⟨j, hj, hcoeff⟩ := exists_nonzero_variation_component f z v n hn
  refine ⟨j, ?_, hcoeff⟩
  by_contra hlt
  have hz := variation_eq_zero_of_wordDegree_lt
    (p := p) (hp := hp) (δ := δ) (η := η) (h := h) f z v j (by omega)
  rw [hz] at hcoeff
  exact hcoeff rfl

end

end MakarLimanov.ResidualHomogeneous
