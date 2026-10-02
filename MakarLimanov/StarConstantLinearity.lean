import MakarLimanov.SymbolSeries

/-!
# Linearity of star products over differential constants

Left multiplication is linear over constants of the Euler derivation; right
multiplication is linear over constants of the coefficient derivation.
-/

noncomputable section

namespace MakarLimanov.StarConstantLinearity

open HahnSeries SymbolSeries

attribute [local instance 2000] HahnSeries.instAlgebra

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A constant of `eta` factors out of the left star factor. -/
theorem starProduct_smul_left_of_eq_zero
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F) (a : F) (ha : η a = 0)
    (x y : LaurentSeries F) :
    starProduct p hp δ η (a • x) y = a • starProduct p hp δ η x y := by
  have hterm (i : ℕ) : starTerm p δ η (a • x) y i = a • starTerm p δ η x y i := by
    simp only [starTerm, deltaOperator_iterate_smul_of_eq_zero p η a ha,
      smul_mul_assoc]
    all_goals
      exact smul_comm ((i.factorial : F)⁻¹) a
        ((deltaOperator p η)^[i] x * (coefficientDerivation δ)^[i] y)
  ext n
  simp only [starProduct_coeff, hterm, coeff_smul, smul_finsum]

/-- A constant of `delta` factors out of the right star factor. -/
theorem starProduct_smul_right_of_eq_zero
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F) (a : F) (ha : δ a = 0)
    (x y : LaurentSeries F) :
    starProduct p hp δ η x (a • y) = a • starProduct p hp δ η x y := by
  have hterm (i : ℕ) : starTerm p δ η x (a • y) i = a • starTerm p δ η x y i := by
    simp only [starTerm, coefficientDerivation_iterate_smul_of_eq_zero δ a ha,
      mul_smul_comm]
    all_goals
      exact smul_comm ((i.factorial : F)⁻¹) a
        ((deltaOperator p η)^[i] x * (coefficientDerivation δ)^[i] y)
  ext n
  simp only [starProduct_coeff, hterm, coeff_smul, smul_finsum]

/-- Star multiplication distributes over a finite sum in its left factor. -/
theorem starProduct_sum_left
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    {ι : Type*} (s : Finset ι) (x : ι → LaurentSeries F) (y : LaurentSeries F) :
    starProduct p hp δ η (∑ i ∈ s, x i) y = ∑ i ∈ s, starProduct p hp δ η (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, starProduct_add_left, ih]

/-- Star multiplication distributes over a finite sum in its right factor. -/
theorem starProduct_sum_right
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x : LaurentSeries F) {ι : Type*} (s : Finset ι) (y : ι → LaurentSeries F) :
    starProduct p hp δ η x (∑ i ∈ s, y i) = ∑ i ∈ s, starProduct p hp δ η x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, starProduct_add_right, ih]

variable {C : Type*} [Field C] [Algebra C F]

/-- Linearity over a coefficient field killed by the Euler derivation. -/
theorem starProduct_C_smul_left
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hη : ∀ a : C, η (algebraMap C F a) = 0)
    (a : C) (x y : LaurentSeries F) :
    starProduct p hp δ η (a • x) y = a • starProduct p hp δ η x y := by
  simpa only [algebraMap_smul] using
    starProduct_smul_left_of_eq_zero p hp δ η (algebraMap C F a) (hη a) x y

/-- Linearity over a coefficient field killed by the coefficient derivation. -/
theorem starProduct_C_smul_right
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hδ : ∀ a : C, δ (algebraMap C F a) = 0)
    (a : C) (x y : LaurentSeries F) :
    starProduct p hp δ η x (a • y) = a • starProduct p hp δ η x y := by
  simpa only [algebraMap_smul] using
    starProduct_smul_right_of_eq_zero p hp δ η (algebraMap C F a) (hδ a) x y

end MakarLimanov.StarConstantLinearity
