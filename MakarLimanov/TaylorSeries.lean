import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Taylor series of field derivations, constructed coefficient by coefficient. -/

namespace MakarLimanov.TaylorSeries
open Finset
variable {k F : Type*} [CommRing k] [Field F] [CharZero F] [Algebra k F]

omit [CharZero F] in
lemma iterate_mul (D : Derivation k F F) (n : ℕ) (x y : F) :
    D^[n] (x * y) = ∑ ab ∈ Finset.antidiagonal n,
      n.choose ab.1 • (D^[ab.1] x * D^[ab.2] y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (fun a b ↦ D^[a] x * D^[b] y) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, smul_add, sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro ab hab
    rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hab).symm]
    ring

lemma factorial_coefficient (a b : ℕ) :
    (((a+b).factorial : F)⁻¹ * ((a+b).choose a : F)) =
      (a.factorial : F)⁻¹ * (b.factorial : F)⁻¹ := by
  have hf : ((a+b).choose a : F) * a.factorial * b.factorial = (a+b).factorial := by
    rw [Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial a b
  have ha : (a.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr a.factorial_ne_zero
  have hb : (b.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr b.factorial_ne_zero
  have hab : ((a+b).factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr (a+b).factorial_ne_zero
  field_simp
  linear_combination hf

noncomputable def series (D : Derivation k F F) (a : F) : PowerSeries F :=
  PowerSeries.mk (fun n ↦ (n.factorial : F)⁻¹ * D^[n] a)

omit [CharZero F] in
@[simp] lemma coeff_series (D : Derivation k F F) (a : F) (n : ℕ) :
    PowerSeries.coeff n (series D a) = (n.factorial : F)⁻¹ * D^[n] a :=
  PowerSeries.coeff_mk _ _

lemma series_mul (D : Derivation k F F) (a b : F) :
    series D (a*b) = series D a * series D b := by
  ext n
  rw [coeff_series, iterate_mul, PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  have hn := Finset.mem_antidiagonal.mp hij
  simp only [coeff_series, nsmul_eq_mul]
  have hf : (n.factorial : F)⁻¹ * (n.choose i : F) =
      (i.factorial : F)⁻¹ * (j.factorial : F)⁻¹ := by
    rw [← hn]
    exact factorial_coefficient i j
  calc
    _ = ((n.factorial : F)⁻¹ * (n.choose i : F)) * (D^[i] a * D^[j] b) := by ring
    _ = _ := by rw [hf]; ring

omit [CharZero F] in
lemma iterate_add (D : Derivation k F F) (n : ℕ) (a b : F) :
    D^[n] (a+b) = D^[n] a + D^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih]

omit [CharZero F] in
lemma iterate_algebraMap (D : Derivation k F F) (a : k) (n : ℕ) :
    D^[n] (algebraMap k F a) = if n = 0 then algebraMap k F a else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0 <;> simp [Function.iterate_succ_apply', ih, hn]

/-- The unital algebra map whose coefficients are the divided iterates of a derivation. -/
noncomputable def taylor (D : Derivation k F F) : F →ₐ[k] PowerSeries F where
  toFun := series D
  map_zero' := by
    ext n
    have h : D^[n] 0 = 0 := by simpa using iterate_algebraMap D (0 : k) n
    simp [coeff_series, h]
  map_one' := by
    ext n
    have h := iterate_algebraMap D (1 : k) n
    simp only [map_one] at h
    rw [coeff_series, h]
    by_cases hn : n = 0 <;> simp [hn, PowerSeries.coeff_one]
  map_add' a b := by ext n; simp [coeff_series, mul_add]
  map_mul' := series_mul D
  commutes' a := by
    ext n
    rw [coeff_series, iterate_algebraMap]
    by_cases hn : n = 0 <;> simp [hn, PowerSeries.algebraMap_apply, PowerSeries.coeff_C]

@[simp] lemma taylor_apply (D : Derivation k F F) (a : F) : taylor D a = series D a := rfl

@[simp] lemma constantCoeff_taylor (D : Derivation k F F) (a : F) :
    PowerSeries.constantCoeff (taylor D a) = a := by
  change PowerSeries.constantCoeff (series D a) = a
  simp [series]

lemma taylor_injective (D : Derivation k F F) : Function.Injective (taylor D) :=
  (taylor D).injective

/-- Formal differentiation of the Taylor series implements the original derivation. -/
lemma derivative_taylor (D : Derivation k F F) (a : F) :
    PowerSeries.derivative F (taylor D a) = taylor D (D a) := by
  ext n
  rw [PowerSeries.coeff_derivative]
  rw [taylor_apply, taylor_apply, coeff_series, coeff_series]
  rw [Function.iterate_succ_apply, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n+1 : F) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

omit [CharZero F] in
lemma iterate_mul_constant (D : Derivation k F F) (c : F) (hc : D c = 0)
    (n : ℕ) (a : F) : D^[n] (c*a) = c * D^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih, Derivation.leibniz, hc, mul_comm]

/-- Double Taylor map, represented by a power series whose coefficients are power series. -/
noncomputable def doubleTaylor (δ η : Derivation k F F) : F →ₐ[k] PowerSeries (PowerSeries F) :=
  (PowerSeries.mapAlgHom (taylor η)).comp (taylor δ)

lemma doubleTaylor_coeff (δ η : Derivation k F F) (a : F) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (doubleTaylor δ η a)) =
      (i.factorial : F)⁻¹ * (j.factorial : F)⁻¹ * η^[j] (δ^[i] a) := by
  change PowerSeries.coeff j (PowerSeries.coeff i
    (PowerSeries.map (taylor η).toRingHom (series δ a))) = _
  rw [PowerSeries.coeff_map]
  change PowerSeries.coeff j (series η (PowerSeries.coeff i (series δ a))) = _
  rw [coeff_series, coeff_series,
    iterate_mul_constant η _ (by
      have hf : (i.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
      have hh := η.leibniz (i.factorial : F) (i.factorial : F)⁻¹
      simp [hf] at hh
      exact hh) j]
  ring

lemma doubleTaylor_coeff_commute (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (a : F) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (doubleTaylor δ η a)) =
      (i.factorial : F)⁻¹ * (j.factorial : F)⁻¹ * δ^[i] (η^[j] a) := by
  rw [doubleTaylor_coeff, ((hc.iterate_left i).iterate_right j) a]

lemma doubleTaylor_injective (δ η : Derivation k F F) :
    Function.Injective (doubleTaylor δ η) := (doubleTaylor δ η).injective

@[simp] lemma doubleTaylor_constant (δ η : Derivation k F F) (a : F) :
    PowerSeries.constantCoeff (PowerSeries.constantCoeff (doubleTaylor δ η a)) = a := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_mul, Function.iterate_zero_apply] using
    doubleTaylor_coeff δ η a 0 0
end MakarLimanov.TaylorSeries
