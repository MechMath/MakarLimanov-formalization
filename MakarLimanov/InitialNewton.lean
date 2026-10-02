import MakarLimanov.BinarySupport
import MakarLimanov.SymbolSeries

/-! The initial zero symbol in the binary commutator branch. -/

namespace MakarLimanov.InitialNewton

open MakarLimanov SymbolSeries SymbolSeries.StarSeries

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero F]

theorem lift_zero_true_of_binaryAbelianize_zero
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0)
    (p : ℕ) (hp : 0 < p)
    (δ η : Derivation K F F) (hc : Function.Commute δ η) :
    toSeries (evaluateAt (hp := hp) (h := hc) (0 : LaurentSeries F) g) = 0 := by
  rw [evaluateAt, evaluatePair, evaluate]
  rw [ControlledMatrix.lift_eq_word_sum]
  simp only [toSeries]
  calc
    (ControlledMatrix.wordCoefficients g).sum
        (fun w c ↦ c •
          (List.map (fun b ↦ ofSeries (if b then 0 else distinguishedSymbol p))
            w.toList).prod) =
      (ControlledMatrix.wordCoefficients g).sum (fun _ _ ↦ 0) := by
      apply Finsupp.sum_congr
      intro w hw
      by_cases ht : true ∈ w.toList
      · obtain ⟨u, v, huv⟩ := List.mem_iff_append.mp ht
        rw [huv]
        simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons]
        change _ • (_ * ((ofSeries (hp := hp) (h := hc) (0 : LaurentSeries F)) * _)) = 0
        have hz : (ofSeries (hp := hp) (h := hc) (0 : LaurentSeries F) :
            StarSeries p hp δ η hc) = 0 := rfl
        rw [hz, zero_mul, mul_zero, smul_zero]
      · have hfalse : w.toList = List.replicate w.toList.length false := by
          apply List.eq_replicate_of_mem
          intro b hb
          cases b with
          | false => rfl
          | true => exact False.elim (ht hb)
        have hw : w = FreeMonoid.ofList (List.replicate w.toList.length false) :=
          FreeMonoid.toList.injective hfalse
        have hc0 : (ControlledMatrix.wordCoefficients g) w = 0 := by
          change (ControlledMatrix.wordCoefficients g) w = 0
          rw [hw]
          rw [← BinarySupport.pure_coefficient g false w.toList.length, hg]
          simp
        rw [hc0]
        exact zero_smul _ _
    _ = 0 := Finsupp.sum_fun_zero _

theorem initial_residual
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0)
    (p : ℕ) (hp : 0 < p)
    (δ η : Derivation K F F) (hc : Function.Commute δ η) :
    toSeries (evaluateAt (hp := hp) (h := hc) (0 : LaurentSeries F) (1 + g)) = 1 := by
  rw [map_add, map_one, toSeries_add, lift_zero_true_of_binaryAbelianize_zero g hg p hp δ η hc]
  simp

theorem initial_stage_data
    (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0)
    (p : ℕ) (hp : 0 < p)
    (δ η : Derivation K F F) (hc : Function.Commute δ η) :
    (0 : LaurentSeries F).support.Finite ∧
      LowerBound 0 (0 : LaurentSeries F) ∧
      LowerBound 0
        (toSeries (evaluateAt (hp := hp) (h := hc) (0 : LaurentSeries F) (1 + g))) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro n hn
    exact HahnSeries.coeff_zero
  · rw [initial_residual g hg p hp δ η hc]
    intro n hn
    have hn0 : n ≠ 0 := ne_of_lt hn
    simp [HahnSeries.coeff_one, hn0]

end
end MakarLimanov.InitialNewton
