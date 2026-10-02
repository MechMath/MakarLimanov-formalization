import Mathlib.Tactic

/-!
# The denominator divisibility used in the Newton ramification budget

If a rational slope has reduced denominator `b` and an old lattice has
denominator `p`, the refinement factor is `b / gcd p b`.  The elementary
divisibility step in equation (5.3) says that this factor divides every
active degree `k` for which `p * k * slope` is integral.
-/

namespace MakarLimanov.LatticeDenominator

/- The purely arithmetic core of (5.3). -/
theorem refinement_factor_dvd_of_dvd_mul
    (p b k : ℕ) (hp : 0 < p) (hb : 0 < b)
    (h : b ∣ p * k) : b / Nat.gcd p b ∣ k := by
  let g := Nat.gcd p b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b hp
  have hgp : g ∣ p := Nat.gcd_dvd_left p b
  have hgb : g ∣ b := Nat.gcd_dvd_right p b
  have hcop : (p / g).Coprime (b / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hb' : b = g * (b / g) := by
    calc
      b = (b / g) * g := (Nat.div_mul_cancel hgb).symm
      _ = g * (b / g) := by ac_rfl
  have hp' : p = g * (p / g) := by
    calc
      p = (p / g) * g := (Nat.div_mul_cancel hgp).symm
      _ = g * (p / g) := by ac_rfl
  have hscaled : g * (b / g) ∣ g * ((p / g) * k) := by
    rw [hb', hp'] at h
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hquot : b / g ∣ (p / g) * k :=
    Nat.dvd_of_mul_dvd_mul_left hg hscaled
  exact hcop.symm.dvd_of_dvd_mul_left hquot

/-- A natural-number multiple of a rational number is integral only if its
reduced denominator divides that multiplier. -/
theorem den_dvd_of_nat_mul_eq_intCast
    (s : ℚ) (n : ℕ) (a : ℤ) (h : (n : ℚ) * s = a) :
    s.den ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hs : s = Rat.divInt a n := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    apply (eq_div_iff hnQ).mpr
    simpa [mul_comm] using h
  have hd := Rat.den_dvd a n
  rw [← hs] at hd
  exact Int.natCast_dvd_natCast.mp hd

/-- On the old `1/p` lattice, an active Newton equality forces the new
refinement factor to divide the homogeneous degree. -/
theorem refinement_factor_dvd_of_order_equality
    (s : ℚ) (p j : ℕ) (hp : 0 < p) (a r : ℤ)
    (h : (j : ℚ) * s + (a : ℚ) / p = (r : ℚ) / p) :
    s.den / Nat.gcd p s.den ∣ j := by
  apply refinement_factor_dvd_of_dvd_mul p s.den j hp s.den_pos
  apply den_dvd_of_nat_mul_eq_intCast s (p * j) (r - a)
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  field_simp at h
  push_cast
  nlinarith

end MakarLimanov.LatticeDenominator
