import MakarLimanov.BinarySupport
import MakarLimanov.SymbolSeries

/-!
# The initial Newton residual

The zero Abelianized part contains no pure word.  Evaluating the second
generator at zero therefore kills every support word, because the actual star
algebra is a unital algebra with zero absorbing on either side.
-/

namespace MakarLimanov.InitialResidual

open BinarySupport ControlledMatrix SymbolSeries SymbolSeries.StarSeries

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

theorem evaluateAt_zero_of_abelianize_zero
    {p : ℕ} (hp : 0 < p) (δ η : Derivation K K K) (hc : Function.Commute δ η)
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0) :
    toSeries (evaluateAt (hp := hp) (h := hc) (0 : LaurentSeries K) g) = 0 := by
  change toSeries (FreeAlgebra.lift K
    (fun b : Bool ↦ ofSeries (if b then (0 : LaurentSeries K)
      else distinguishedSymbol p)) g) = 0
  rw [ControlledMatrix.lift_eq_word_sum]
  classical
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨_, ht⟩ := support_contains_both g hg w hw
  have hz : 0 ∈ w.toList.map (fun b : Bool ↦
      ofSeries (hp := hp) (h := hc)
        (if b then (0 : LaurentSeries K) else distinguishedSymbol p)) := by
    exact List.mem_map.mpr ⟨true, ht, by
      change (0 : StarSeries p hp δ η hc) = 0
      rfl⟩
  rw [List.prod_eq_zero hz]
  simp only [smul_zero]
  rfl

theorem initial_residual_lowerBound
    {p : ℕ} (hp : 0 < p) (δ η : Derivation K K K) (hc : Function.Commute δ η)
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0) :
    LowerBound 0 (toSeries (evaluateAt (hp := hp) (h := hc)
      (0 : LaurentSeries K) g)) := by
  rw [evaluateAt_zero_of_abelianize_zero hp δ η hc g hg]
  intro n hn
  rfl

theorem evaluateAt_zero_one_add
    {p : ℕ} (hp : 0 < p) (δ η : Derivation K K K) (hc : Function.Commute δ η)
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0) :
    toSeries (evaluateAt (hp := hp) (h := hc) (0 : LaurentSeries K) (1 + g)) = 1 := by
  rw [map_add, map_one]
  simp only [toSeries_add, toSeries_one]
  rw [evaluateAt_zero_of_abelianize_zero hp δ η hc g hg]
  simp

theorem evaluateAt_zero_one_add_lowerBound
    {p : ℕ} (hp : 0 < p) (δ η : Derivation K K K) (hc : Function.Commute δ η)
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0) :
    LowerBound 0 (toSeries (evaluateAt (hp := hp) (h := hc)
      (0 : LaurentSeries K) (1 + g))) := by
  rw [evaluateAt_zero_one_add hp δ η hc g hg]
  intro n hn
  simp [ne_of_lt hn]

end

end MakarLimanov.InitialResidual
