import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Rational slopes on refined lattices

The denominator factor `den(s) / gcd(p, den(s))` makes `p * e * s` integral.
It need not make `e * s` integral unless the original denominator is coprime
to `p`.
-/

namespace MakarLimanov.RationalSlopeRefinement

def refinementFactor (p : ℕ) (s : ℚ) : ℕ :=
  s.den / Nat.gcd p s.den

theorem refinementFactor_pos (p : ℕ) (hp : 0 < p) (s : ℚ) :
    0 < refinementFactor p s := by
  have hgpos : 0 < Nat.gcd p s.den := Nat.gcd_pos_of_pos_left s.den hp
  have hgdiv : Nat.gcd p s.den ∣ s.den := Nat.gcd_dvd_right p s.den
  have hgle : Nat.gcd p s.den ≤ s.den := Nat.le_of_dvd s.den_pos hgdiv
  exact Nat.div_pos hgle hgpos

theorem denominator_dvd_refined_product (p : ℕ) (s : ℚ) :
    s.den ∣ p * refinementFactor p s := by
  let g := Nat.gcd p s.den
  have hgp : g ∣ p := Nat.gcd_dvd_left p s.den
  have hgs : g ∣ s.den := Nat.gcd_dvd_right p s.den
  have hp : p / g * g = p := Nat.div_mul_cancel hgp
  have hs : s.den / g * g = s.den := Nat.div_mul_cancel hgs
  refine ⟨p / g, ?_⟩
  dsimp [refinementFactor, g]
  calc
    p * (s.den / Nat.gcd p s.den) =
        (p / Nat.gcd p s.den * Nat.gcd p s.den) *
          (s.den / Nat.gcd p s.den) := by rw [hp]
    _ = (s.den / Nat.gcd p s.den * Nat.gcd p s.den) *
          (p / Nat.gcd p s.den) := by ac_rfl
    _ = s.den * (p / Nat.gcd p s.den) := by rw [hs]

private theorem exists_integer_multiple_of_denominator
    (s : ℚ) (n : ℕ) (hden : s.den ∣ n) :
    ∃ a : ℤ, (a : ℚ) = (n : ℚ) * s := by
  let a : ℤ := s.num * (n / s.den : ℕ)
  have hdiv := Nat.div_mul_cancel hden
  have hdivQ : (s.den : ℚ) * (n / s.den : ℕ) = (n : ℚ) := by
    exact_mod_cast (by simpa [mul_comm] using hdiv)
  refine ⟨a, ?_⟩
  dsimp [a]
  simp only [Int.cast_mul]
  calc
    (s.num : ℚ) * (n / s.den : ℕ) =
        ((s.num : ℚ) / (s.den : ℚ)) *
          ((s.den : ℚ) * (n / s.den : ℕ)) := by field_simp
    _ = (n : ℚ) * s := by rw [Rat.num_div_den, hdivQ]; ring

/-- The denominator refinement makes the exponent at denominator `p * e`
integral. -/
theorem exists_refined_numerator (p : ℕ) (s : ℚ) :
    ∃ q' : ℤ,
      (q' : ℚ) = (p * refinementFactor p s : ℕ) * s := by
  exact exists_integer_multiple_of_denominator s (p * refinementFactor p s)
    (denominator_dvd_refined_product p s)

/-- The integral refined numerator recovers the same rational slope. -/
theorem refined_numerator_div (p : ℕ) (hp : 0 < p) (s : ℚ)
    (q' : ℤ) (hq' : (q' : ℚ) = (p * refinementFactor p s : ℕ) * s) :
    (q' : ℚ) / (p * refinementFactor p s : ℕ) = s := by
  have hpos := Nat.mul_pos hp (refinementFactor_pos p hp s)
  have hne : (p * refinementFactor p s : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [hq']
  field_simp

/-- Package the positive refinement factor, integral numerator, and quotient
identity at the refined denominator. -/
theorem exists_refinement_data (p : ℕ) (hp : 0 < p) (s : ℚ) :
    ∃ e : ℕ, ∃ q' : ℤ,
      e = refinementFactor p s ∧ 0 < e ∧
      (q' : ℚ) = (p * e : ℕ) * s ∧
      (q' : ℚ) / (p * e : ℕ) = s := by
  let e := refinementFactor p s
  obtain ⟨q', hq'⟩ := exists_refined_numerator p s
  refine ⟨e, q', rfl, refinementFactor_pos p hp s, hq', ?_⟩
  exact refined_numerator_div p hp s q' hq'

/-- As a rational identity, `(p*e)*s/p = e*s` for positive `p`. -/
theorem refined_slope_identity (p e : ℕ) (hp : 0 < p) (s : ℚ) :
    (p * e : ℕ) * s / p = (e : ℚ) * s := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpQ]
  push_cast
  ring

/-- If `p` is coprime to the reduced denominator, the factor also makes
`e*s` integral, exactly as in the stronger special-case form. -/
theorem exists_refinement_factor_times_slope_integer
    (p : ℕ) (s : ℚ) (hc : Nat.Coprime p s.den) :
    ∃ q' : ℤ,
      (q' : ℚ) = (refinementFactor p s : ℕ) * s := by
  refine ⟨s.num, ?_⟩
  have hg : Nat.gcd p s.den = 1 := hc.gcd_eq_one
  rw [refinementFactor, hg]
  norm_num

/-- The stronger `e*s` numerator requested in some slope conventions is
available when the reduced denominator is coprime to the old denominator. -/
theorem exists_coprime_refinement_data
    (p : ℕ) (hp : 0 < p) (s : ℚ) (hc : Nat.Coprime p s.den) :
    ∃ e : ℕ, ∃ q' : ℤ,
      e = refinementFactor p s ∧ 0 < e ∧
      (q' : ℚ) = (p * e : ℕ) * s / p ∧
      (q' : ℚ) = (e : ℚ) * s := by
  let e := refinementFactor p s
  obtain ⟨q', hq'⟩ := exists_refinement_factor_times_slope_integer p s hc
  refine ⟨e, q', rfl, refinementFactor_pos p hp s, ?_, hq'⟩
  rw [refined_slope_identity p e hp s, hq']

/-- Multiplication by a positive refinement factor preserves strict slope
inequalities when the scaled rational is integral. -/
theorem refined_numerator_gt
    (e : ℕ) (he : 0 < e) (s q : ℚ) (q' : ℤ)
    (hq' : (q' : ℚ) = (e : ℚ) * s) (hs : q < s) :
    (e : ℚ) * q < (q' : ℚ) := by
  rw [hq']
  exact mul_lt_mul_of_pos_left hs (by exact_mod_cast he)

end MakarLimanov.RationalSlopeRefinement
