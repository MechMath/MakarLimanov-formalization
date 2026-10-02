import MakarLimanov.Variations
import MakarLimanov.CentralTwist

/-! Exact central-twist identities for the actual variations in the symbol algebra. -/

namespace MakarLimanov.SymbolVariations

open SymbolSeries SymbolSeries.StarSeries HahnSeries

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]
variable {p : ℕ} {hp : 0 < p} {δ η : Derivation k F F} {h : Function.Commute δ η}

/-- The nth variation of `f(D,Z)` as an ordinary Laurent coefficient sequence. -/
def variation (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℕ) : LaurentSeries F :=
  toSeries (Variations.variation f (ofSeries (distinguishedSymbol p))
    (ofSeries (hp := hp) (h := h) z) (ofSeries v) n)

private theorem central_commute (c : LaurentSeries F)
    (hΔ : deltaOperator p η c = 0) (hδ : coefficientDerivation δ c = 0)
    (a : StarSeries p hp δ η h) : Commute a (ofSeries c) := by
  change starProduct p hp δ η (toSeries a) c = starProduct p hp δ η c (toSeries a)
  obtain ⟨hl, hr⟩ := starProduct_central p hp δ η c (toSeries a) hΔ hδ
  exact hr.trans hl.symm

private theorem central_pow (c : LaurentSeries F)
    (hδ : coefficientDerivation δ c = 0) (n : ℕ) :
    toSeries ((ofSeries (hp := hp) (h := h) c) ^ n) = c ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, toSeries_mul, ih, toSeries_ofSeries,
      starProduct_eq_mul_of_coefficientDerivation_eq_zero p hp δ η _ _ hδ, pow_succ]

/-- The central factor acts by ordinary Laurent multiplication, with an exact nth power. -/
theorem central_mul (f : FreeAlgebra k Bool) (z v c : LaurentSeries F)
    (hΔ : deltaOperator p η c = 0) (hδ : coefficientDerivation δ c = 0) (n : ℕ) :
    variation (hp := hp) (h := h) f z (c * v) n =
      c ^ n * variation (hp := hp) (h := h) f z v n := by
  have hcv : ofSeries (hp := hp) (h := h) (c * v) = ofSeries c * ofSeries v :=
    (starProduct_eq_mul_of_delta_eq_zero p hp δ η c v hΔ).symm
  unfold variation
  rw [hcv, Variations.variation_central_mul _ _ _ _ _ (central_commute c hΔ hδ),
    toSeries_mul, central_pow c hδ]
  apply starProduct_eq_mul_of_delta_eq_zero
  simp [Derivation.leibniz_pow, hΔ]

/-- A nonzero central twist preserves vanishing of each variation. -/
theorem central_mul_eq_zero_iff (f : FreeAlgebra k Bool) (z v c : LaurentSeries F)
    (hc : c ≠ 0) (hΔ : deltaOperator p η c = 0)
    (hδ : coefficientDerivation δ c = 0) (n : ℕ) :
    variation (hp := hp) (h := h) f z (c * v) n = 0 ↔
      variation (hp := hp) (h := h) f z v n = 0 := by
  rw [central_mul f z v c hΔ hδ n]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero n hc))

/-- An eigenvector monomial gives the central twist required for changing slopes. -/
theorem monomial_mul (f : FreeAlgebra k Bool) (z v : LaurentSeries F)
    (a : F) (q : ℤ) (haδ : δ a = 0) (haη : η a = (p : F)⁻¹ * (q : F) * a) (n : ℕ) :
    variation (hp := hp) (h := h) f z (single q a * v) n =
      single ((n : ℤ) * q) (a ^ n) * variation (hp := hp) (h := h) f z v n := by
  obtain ⟨hΔ, hδ⟩ := monomial_twist_killed p δ η q a haδ haη
  rw [central_mul f z v (single q a) hΔ hδ n, single_pow, nsmul_eq_mul]

/-- The lower Laurent index changes exactly by `n*q`; this is not only a support bound. -/
theorem monomial_order (f : FreeAlgebra k Bool) (z v : LaurentSeries F)
    (a : F) (ha : a ≠ 0) (q : ℤ)
    (haδ : δ a = 0) (haη : η a = (p : F)⁻¹ * (q : F) * a) (n : ℕ)
    (hv : variation (hp := hp) (h := h) f z v n ≠ 0) :
    (variation (hp := hp) (h := h) f z (single q a * v) n).order =
      (n : ℤ) * q + (variation (hp := hp) (h := h) f z v n).order := by
  rw [monomial_mul f z v a q haδ haη n]
  exact order_single_mul_of_isRegular (IsRegular.of_ne_zero (pow_ne_zero n ha)) hv

/-- Exact change of the actual Laurent variations after adding the correction. -/
theorem variation_shift (f : FreeAlgebra k Bool) (z v : LaurentSeries F) (n : ℕ) :
    variation (hp := hp) (h := h) f (z + v) v n =
      ∑ j ∈ (Variations.expansion (ofSeries (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := h) z) (ofSeries v) f).support,
        (j.choose n) • variation (hp := hp) (h := h) f z v j := by
  let ψ : StarSeries p hp δ η h →+ LaurentSeries F :=
    { toFun := toSeries, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have heq := congrArg ψ (Variations.variation_shift f
    (ofSeries (distinguishedSymbol p)) (ofSeries (hp := hp) (h := h) z)
    (ofSeries v) n)
  change ψ (Variations.variation f
    (ofSeries (hp := hp) (h := h) (distinguishedSymbol p))
    (ofSeries (hp := hp) (h := h) z + ofSeries (hp := hp) (h := h) v)
    (ofSeries (hp := hp) (h := h) v) n) = _
  rw [heq, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← nsmul_eq_mul', map_nsmul]
  rfl

end

end MakarLimanov.SymbolVariations
