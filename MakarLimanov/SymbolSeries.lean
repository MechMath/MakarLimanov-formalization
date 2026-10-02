import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.FreeAlgebra

/-!
# Concrete differential operators on the submitted symbol series

For a denominator `p`, Laurent index `n` represents the symbol exponent `-n / p`.
The coefficient derivation and the shifted Euler derivation below are concrete
operators on Laurent series, independent of the as yet unconstructed star product.
-/

noncomputable section

open HahnSeries Finset

-- Use the coefficient algebra structure, not the distinct power-series tower instance.
attribute [local instance 2000] HahnSeries.instAlgebra

namespace MakarLimanov.SymbolSeries

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Apply a field derivation to every coefficient of a Laurent series. -/
def coefficientMap (d : Derivation k F F) (x : LaurentSeries F) : LaurentSeries F :=
  x.map d.toLinearMap

@[simp] theorem coefficientMap_coeff (d : Derivation k F F) (x : LaurentSeries F) (n : ℤ) :
    (coefficientMap d x).coeff n = d (x.coeff n) := rfl

theorem coefficientMap_support_subset (d : Derivation k F F) (x : LaurentSeries F) :
    (coefficientMap d x).support ⊆ x.support := by
  intro n hn
  simp only [mem_support, coefficientMap_coeff] at hn ⊢
  exact fun h ↦ hn (by simp [h])

theorem coefficientMap_mul (d : Derivation k F F) (x y : LaurentSeries F) :
    coefficientMap d (x * y) = x * coefficientMap d y + y * coefficientMap d x := by
  ext n
  rw [coeff_add, mul_comm y, coefficientMap_coeff, coeff_mul,
    coeff_mul_right' y.isPWO_support (coefficientMap_support_subset d y),
    coeff_mul_left' x.isPWO_support (coefficientMap_support_subset d x)]
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, coefficientMap_coeff, sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro ij hij
  ring

/-- The coefficient operator as a derivation of the ordinary Laurent series algebra. -/
def coefficientDerivation (d : Derivation k F F) :
    Derivation k (LaurentSeries F) (LaurentSeries F) where
  toFun := coefficientMap d
  map_add' x y := by ext n; simp [coefficientMap]
  map_smul' c x := by
    ext n
    change d (c • x.coeff n) = c • d (x.coeff n)
    exact d.map_smul c (x.coeff n)
  map_one_eq_zero' := by ext n; by_cases hn : n = 0 <;> simp [coefficientMap, hn]
  leibniz' x y := coefficientMap_mul d x y

@[simp] theorem coefficientDerivation_coeff (d : Derivation k F F)
    (x : LaurentSeries F) (n : ℤ) :
    (coefficientDerivation d x).coeff n = d (x.coeff n) := rfl

/-- The Euler operator, multiplying the coefficient at `n` by the integer `n`. -/
def eulerMap (x : LaurentSeries F) : LaurentSeries F where
  coeff n := (n : F) * x.coeff n
  isPWO_support' := x.isPWO_support.mono <| by
    intro n hn
    simp only [Function.mem_support] at hn ⊢
    exact fun h ↦ hn (by simp [h])

@[simp] theorem eulerMap_coeff (x : LaurentSeries F) (n : ℤ) :
    (eulerMap x).coeff n = (n : F) * x.coeff n := rfl

theorem eulerMap_support_subset (x : LaurentSeries F) :
    (eulerMap x).support ⊆ x.support := by
  intro n hn
  simp only [mem_support, eulerMap_coeff] at hn ⊢
  exact fun h ↦ hn (by simp [h])

theorem eulerMap_mul (x y : LaurentSeries F) :
    eulerMap (x * y) = x * eulerMap y + y * eulerMap x := by
  ext n
  rw [coeff_add, mul_comm y, eulerMap_coeff, coeff_mul,
    coeff_mul_right' y.isPWO_support (eulerMap_support_subset y),
    coeff_mul_left' x.isPWO_support (eulerMap_support_subset x), mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := (mem_addAntidiagonal.mp hij).2.2
  simp only [eulerMap_coeff]
  rw [← hn, Int.cast_add]
  ring

/-- The Euler operator as a derivation over the constant base field. -/
def eulerDerivation : Derivation k (LaurentSeries F) (LaurentSeries F) where
  toFun := eulerMap
  map_add' x y := by ext n; simp [mul_add]
  map_smul' c x := by
    ext n
    change (n : F) * (c • x.coeff n) = c • ((n : F) * x.coeff n)
    exact mul_smul_comm _ _ _
  map_one_eq_zero' := by ext n; by_cases hn : n = 0 <;> simp [hn]
  leibniz' x y := eulerMap_mul x y

@[simp] theorem eulerDerivation_coeff (x : LaurentSeries F) (n : ℤ) :
    (eulerDerivation (k := k) x).coeff n = (n : F) * x.coeff n := rfl

/-- The order-lowering operator of equation (3.1), in Laurent coordinates. -/
def deltaOperator (p : ℕ) (η : Derivation k F F) :
    Derivation k (LaurentSeries F) (LaurentSeries F) :=
  (single (p : ℤ) (1 : F) : LaurentSeries F) •
    (coefficientDerivation η - (p : F)⁻¹ • eulerDerivation)

@[simp] theorem deltaOperator_coeff (p : ℕ) (η : Derivation k F F)
    (x : LaurentSeries F) (n : ℤ) :
    (deltaOperator p η x).coeff n =
      η (x.coeff (n - p)) - (p : F)⁻¹ * ((n - p : ℤ) : F) * x.coeff (n - p) := by
  simp [deltaOperator, Derivation.smul_apply, Derivation.sub_apply, smul_eq_mul,
    coeff_single_mul, mul_assoc]

theorem coefficientDerivation_commute (δ η : Derivation k F F)
    (h : Function.Commute δ η) :
    Function.Commute (coefficientDerivation δ) (coefficientDerivation η) := by
  intro x
  ext n
  exact h (x.coeff n)

theorem coefficientDerivation_euler_commute (δ : Derivation k F F) :
    Function.Commute (coefficientDerivation δ) (eulerDerivation (k := k) (F := F)) := by
  intro x
  ext n
  simp [Derivation.leibniz, smul_eq_mul]

theorem coefficientDerivation_delta_commute (p : ℕ) (δ η : Derivation k F F)
    (h : Function.Commute δ η) :
    Function.Commute (coefficientDerivation δ) (deltaOperator p η) := by
  intro x
  ext n
  simp only [coefficientDerivation_coeff, deltaOperator_coeff, map_sub,
    Derivation.leibniz, smul_eq_mul]
  have hp : δ ((p : F)⁻¹) = 0 := by
    rw [Derivation.leibniz_inv]
    simp
  simp only [hp, Derivation.map_intCast, mul_zero, add_zero]
  rw [h]

/-- A concrete integer lower bound on the support in Laurent coordinates. -/
def LowerBound (b : ℤ) (x : LaurentSeries F) : Prop :=
  ∀ n : ℤ, n < b → x.coeff n = 0

theorem lowerBound_order (x : LaurentSeries F) : LowerBound x.order x :=
  fun _ h ↦ coeff_eq_zero_of_lt_order h

theorem LowerBound.mono {b c : ℤ} {x : LaurentSeries F}
    (h : LowerBound b x) (hcb : c ≤ b) : LowerBound c x :=
  fun _ hn ↦ h _ (hn.trans_le hcb)

theorem LowerBound.coefficientDerivation {b : ℤ} {x : LaurentSeries F}
    (h : LowerBound b x) (δ : Derivation k F F) :
    LowerBound b (coefficientDerivation δ x) := by
  intro n hn
  simp [h n hn]

theorem LowerBound.deltaOperator {b : ℤ} {x : LaurentSeries F}
    (h : LowerBound b x) (p : ℕ) (η : Derivation k F F) :
    LowerBound (b + p) (deltaOperator p η x) := by
  intro n hn
  have hnp : n - p < b := by omega
  simp [h (n - p) hnp]

theorem LowerBound.coefficientDerivation_iterate {b : ℤ} {x : LaurentSeries F}
    (h : LowerBound b x) (δ : Derivation k F F) (j : ℕ) :
    LowerBound b ((MakarLimanov.SymbolSeries.coefficientDerivation δ)^[j] x) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using ih.coefficientDerivation δ

theorem LowerBound.deltaOperator_iterate {b : ℤ} {x : LaurentSeries F}
    (h : LowerBound b x) (p : ℕ) (η : Derivation k F F) (j : ℕ) :
    LowerBound (b + (p : ℤ) * j) ((MakarLimanov.SymbolSeries.deltaOperator p η)^[j] x) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    convert ih.deltaOperator p η using 1 <;>
      simp [Function.iterate_succ_apply', mul_add, add_assoc]

theorem LowerBound.mul {b c : ℤ} {x y : LaurentSeries F}
    (hx : LowerBound b x) (hy : LowerBound c y) : LowerBound (b + c) (x * y) := by
  intro n hn
  rw [coeff_mul]
  apply sum_eq_zero
  intro ij hij
  have hi : b ≤ ij.1 := by
    by_contra! hi
    exact (mem_addAntidiagonal.mp hij).1 (hx _ hi)
  have hj : c ≤ ij.2 := by
    by_contra! hj
    exact (mem_addAntidiagonal.mp hij).2.1 (hy _ hj)
  have hs := (mem_addAntidiagonal.mp hij).2.2
  omega

theorem LowerBound.smul {b : ℤ} {x : LaurentSeries F}
    (h : LowerBound b x) (a : F) : LowerBound b (a • x) := by
  intro n hn
  simp [coeff_smul, h n hn]

theorem LowerBound.add {b : ℤ} {x y : LaurentSeries F}
    (hx : LowerBound b x) (hy : LowerBound b y) : LowerBound b (x + y) := by
  intro n hn
  simp [hx n hn, hy n hn]

/-- A family whose lower bounds tend to positive infinity is coefficientwise summable. -/
def summableOfLowerBound (f : ℕ → LaurentSeries F) (b : ℤ)
    (hf : ∀ j : ℕ, LowerBound (b + j) (f j)) : SummableFamily ℤ F ℕ where
  toFun := f
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨b, ?_⟩
    intro n hn
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hn
    change (f j).coeff n ≠ 0 at hj
    by_contra! hnb
    apply hj
    apply hf j
    omega
  finite_co_support' n := by
    apply (Set.finite_Iic (n - b).toNat).subset
    intro j hj
    change j ≤ (n - b).toNat
    have hjn : b + j ≤ n := by
      by_contra! h
      exact hj (hf j n h)
    omega

/-- The j-th summand of equation (3.1), with ordinary multiplication inside each term. -/
def starTerm (p : ℕ) (δ η : Derivation k F F) (x y : LaurentSeries F) (j : ℕ) :
    LaurentSeries F :=
  (j.factorial : F)⁻¹ • ((deltaOperator p η)^[j] x * (coefficientDerivation δ)^[j] y)

theorem starTerm_lowerBound (p : ℕ) (δ η : Derivation k F F)
    {x y : LaurentSeries F} {b c : ℤ} (hx : LowerBound b x) (hy : LowerBound c y)
    (j : ℕ) : LowerBound (b + c + (p : ℤ) * j) (starTerm p δ η x y j) := by
  have h := ((hx.deltaOperator_iterate p η j).mul
    (hy.coefficientDerivation_iterate δ j)).smul (j.factorial : F)⁻¹
  convert h using 1
  ring

/-- The actual locally finite family defining the submitted star product. -/
def starFamily (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) : SummableFamily ℤ F ℕ :=
  summableOfLowerBound (starTerm p δ η x y) (x.order + y.order) fun j ↦
    (starTerm_lowerBound p δ η (lowerBound_order x) (lowerBound_order y) j).mono (by
      have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
      have hj : (0 : ℤ) ≤ j := by omega
      nlinarith)

/-- The symbol star product; no associativity is built into this definition. -/
def starProduct (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) : LaurentSeries F :=
  (starFamily p hp δ η x y).hsum

theorem starProduct_coeff (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) (n : ℤ) :
    (starProduct p hp δ η x y).coeff n = ∑ᶠ j, (starTerm p δ η x y j).coeff n := rfl

/-- Every coefficient of the infinite product is a specified finite sum. -/
theorem starProduct_coeff_finite (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) (n : ℤ) :
    (starProduct p hp δ η x y).coeff n =
      ∑ j ∈ range ((n - (x.order + y.order)).toNat + 1), (starTerm p δ η x y j).coeff n := by
  apply SummableFamily.coeff_hsum_eq_sum_of_subset
  intro j hj
  change (starTerm p δ η x y j).coeff n ≠ 0 at hj
  have hbound := starTerm_lowerBound p δ η (lowerBound_order x) (lowerBound_order y) j
  have hnj : x.order + y.order + (p : ℤ) * j ≤ n := by
    by_contra! h
    exact hj (hbound n h)
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hj' : (0 : ℤ) ≤ j := by omega
  have h : (j : ℤ) ≤ n - (x.order + y.order) := by nlinarith
  change j ∈ range ((n - (x.order + y.order)).toNat + 1)
  rw [mem_range]
  omega

theorem LowerBound.starProduct {b c : ℤ} {x y : LaurentSeries F}
    (hx : LowerBound b x) (hy : LowerBound c y)
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F) :
    LowerBound (b + c) (MakarLimanov.SymbolSeries.starProduct p hp δ η x y) := by
  intro n hn
  rw [starProduct_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  apply starTerm_lowerBound p δ η hx hy j
  have h : (0 : ℤ) ≤ (p : ℤ) * j := mul_nonneg (by omega) (by omega)
  omega

private theorem derivation_iterate_add
    (D : Derivation k (LaurentSeries F) (LaurentSeries F))
    (j : ℕ) (x y : LaurentSeries F) : D^[j] (x + y) = D^[j] x + D^[j] y := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_add]

private theorem derivation_iterate_zero
    (D : Derivation k (LaurentSeries F) (LaurentSeries F)) (j : ℕ) :
    D^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Function.iterate_succ_apply', ih]

private theorem derivation_iterate_one
    (D : Derivation k (LaurentSeries F) (LaurentSeries F)) {j : ℕ} (hj : j ≠ 0) :
    D^[j] 1 = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  simp [Function.iterate_succ_apply]

@[simp] theorem starTerm_zero_index (p : ℕ) (δ η : Derivation k F F)
    (x y : LaurentSeries F) : starTerm p δ η x y 0 = x * y := by
  simp [starTerm]

theorem starTerm_add_left (p : ℕ) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) (j : ℕ) :
    starTerm p δ η (x + y) z j = starTerm p δ η x z j + starTerm p δ η y z j := by
  simp [starTerm, add_mul, smul_add]

theorem starTerm_add_right (p : ℕ) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) (j : ℕ) :
    starTerm p δ η x (y + z) j = starTerm p δ η x y j + starTerm p δ η x z j := by
  simp [starTerm, mul_add, smul_add]

theorem starProduct_add_left (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) :
    starProduct p hp δ η (x + y) z = starProduct p hp δ η x z + starProduct p hp δ η y z := by
  ext n
  simp only [starProduct_coeff, coeff_add]
  simp only [starTerm_add_left, coeff_add]
  exact finsum_add_distrib ((starFamily p hp δ η x z).finite_co_support n)
    ((starFamily p hp δ η y z).finite_co_support n)

theorem starProduct_add_right (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) :
    starProduct p hp δ η x (y + z) = starProduct p hp δ η x y + starProduct p hp δ η x z := by
  ext n
  simp only [starProduct_coeff, coeff_add]
  simp only [starTerm_add_right, coeff_add]
  exact finsum_add_distrib ((starFamily p hp δ η x y).finite_co_support n)
    ((starFamily p hp δ η x z).finite_co_support n)

@[simp] theorem starProduct_one_left (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x : LaurentSeries F) : starProduct p hp δ η 1 x = x := by
  ext n
  rw [starProduct_coeff, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [starTerm, derivation_iterate_one _ hj]

@[simp] theorem starProduct_one_right (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x : LaurentSeries F) : starProduct p hp δ η x 1 = x := by
  ext n
  rw [starProduct_coeff, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [starTerm, derivation_iterate_one _ hj]

@[simp] theorem starProduct_zero_left (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x : LaurentSeries F) : starProduct p hp δ η 0 x = 0 := by
  ext n
  simp [starProduct_coeff, starTerm]

@[simp] theorem starProduct_zero_right (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x : LaurentSeries F) : starProduct p hp δ η x 0 = 0 := by
  ext n
  simp [starProduct_coeff, starTerm]

@[simp] theorem coefficientDerivation_single (δ : Derivation k F F) (n : ℤ) (a : F) :
    coefficientDerivation δ (single n a) = single n (δ a) := by
  ext m
  by_cases hm : m = n <;> simp [hm]

@[simp] theorem eulerDerivation_single (n : ℤ) (a : F) :
    eulerDerivation (k := k) (single n a) = single n ((n : F) * a) := by
  ext m
  by_cases hm : m = n <;> simp [hm]

theorem deltaOperator_single (p : ℕ) (η : Derivation k F F) (n : ℤ) (a : F) :
    deltaOperator p η (single n a) =
      single (n + p) (η a - (p : F)⁻¹ * (n : F) * a) := by
  ext m
  by_cases hm : m = n + p
  · subst m
    simp [deltaOperator_coeff]
  · have hm' : m - p ≠ n := by omega
    simp [deltaOperator_coeff, hm, hm']

/-- The original symbol D has index `-p`. -/
def distinguishedSymbol (p : ℕ) : LaurentSeries F := single (-(p : ℤ)) 1

@[simp] theorem coefficientDerivation_distinguished (p : ℕ) (δ : Derivation k F F) :
    coefficientDerivation δ (distinguishedSymbol p) = 0 := by
  simp [distinguishedSymbol]

@[simp] theorem deltaOperator_distinguished [CharZero F] (p : ℕ) (hp : 0 < p)
    (η : Derivation k F F) : deltaOperator p η (distinguishedSymbol p) = 1 := by
  rw [distinguishedSymbol, deltaOperator_single]
  have hp' : (p : F) ≠ 0 := by exact_mod_cast hp.ne'
  simp [hp']

theorem starProduct_distinguished_right (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (x : LaurentSeries F) :
    starProduct p hp δ η x (distinguishedSymbol p) = x * distinguishedSymbol p := by
  ext n
  rw [starProduct_coeff, finsum_eq_single _ 0]
  · simp
  · intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [starTerm, Function.iterate_succ_apply]

theorem starProduct_distinguished_left [CharZero F] (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (x : LaurentSeries F) :
    starProduct p hp δ η (distinguishedSymbol p) x =
      distinguishedSymbol p * x + coefficientDerivation δ x := by
  have hz (j : ℕ) (hj : j ≠ 0) (hj' : j ≠ 1) :
      starTerm p δ η (distinguishedSymbol p) x j = 0 := by
    have hj1 : 1 ≤ j := by omega
    have hjm : j - 1 ≠ 0 := by omega
    have heq : j = (j - 1) + 1 := by omega
    rw [starTerm, heq, Function.iterate_add_apply]
    simp [deltaOperator_distinguished p hp, derivation_iterate_one _ hjm]
  ext n
  rw [starProduct_coeff, finsum_eq_sum_of_support_subset
    (s := ({0, 1} : Finset ℕ))]
  · simp [starTerm, deltaOperator_distinguished p hp]
  · intro j hj
    by_contra! h
    have hj0 : j ≠ 0 := by simpa using (show j ≠ 0 ∧ j ≠ 1 by simpa using h).1
    have hj1 : j ≠ 1 := (show j ≠ 0 ∧ j ≠ 1 by simpa using h).2
    apply hj
    change (starTerm p δ η (distinguishedSymbol p) x j).coeff n = 0
    rw [hz j hj0 hj1]
    rfl

/-- The commutator identity in equation (3.1) for the actual series product. -/
theorem starProduct_distinguished_commutator [CharZero F] (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (x : LaurentSeries F) :
    starProduct p hp δ η (distinguishedSymbol p) x -
      starProduct p hp δ η x (distinguishedSymbol p) = coefficientDerivation δ x := by
  rw [starProduct_distinguished_left p hp, starProduct_distinguished_right p hp]
  rw [mul_comm x, add_sub_cancel_left]

/-- The Euler map agrees with multiplication by the Laurent variable after differentiation. -/
theorem eulerDerivation_eq_laurentDerivative (x : LaurentSeries F) :
    eulerDerivation (k := k) x = single 1 1 * LaurentSeries.derivative F x := by
  ext n
  simp [coeff_single_mul, LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff]

/-- The coordinate expression `−t^(p+1)/p · d/dt + t^p · η` for Δ. -/
theorem deltaOperator_eq_laurentDerivative (p : ℕ) (η : Derivation k F F)
    (x : LaurentSeries F) :
    deltaOperator p η x =
      -((p : F)⁻¹ • (single ((p : ℤ) + 1) 1 * LaurentSeries.derivative F x)) +
        single (p : ℤ) 1 * coefficientDerivation η x := by
  ext n
  simp only [deltaOperator_coeff, coeff_add, coeff_neg, coeff_smul,
    coeff_single_mul, one_mul, coefficientDerivation_coeff,
    LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff]
  simp
  ring_nf

theorem coefficientDerivation_smul_of_eq_zero (ξ : Derivation k F F) (a : F)
    (ha : ξ a = 0) (x : LaurentSeries F) :
    coefficientDerivation ξ (a • x) = a • coefficientDerivation ξ x := by
  ext n
  simp [coeff_smul, smul_eq_mul, Derivation.leibniz, ha]

theorem coefficientDerivation_starTerm (p : ℕ) (δ η ξ : Derivation k F F)
    (hδ : Function.Commute ξ δ) (hη : Function.Commute ξ η)
    (x y : LaurentSeries F) (j : ℕ) :
    coefficientDerivation ξ (starTerm p δ η x y j) =
      starTerm p δ η (coefficientDerivation ξ x) y j +
        starTerm p δ η x (coefficientDerivation ξ y) j := by
  have hj : ξ ((j.factorial : F)⁻¹) = 0 := by rw [Derivation.leibniz_inv]; simp
  have hΔ := (coefficientDerivation_delta_commute p ξ η hη).iterate_right j
  have hδ' := (coefficientDerivation_commute ξ δ hδ).iterate_right j
  simp only [starTerm, coefficientDerivation_smul_of_eq_zero ξ _ hj,
    Derivation.leibniz, smul_eq_mul, smul_add]
  rw [hΔ x, hδ' y]
  simp only [mul_comm, add_comm]

/-- A commuting field derivation differentiates the actual infinite star product. -/
theorem coefficientDerivation_starProduct (p : ℕ) (hp : 0 < p)
    (δ η ξ : Derivation k F F) (hδ : Function.Commute ξ δ) (hη : Function.Commute ξ η)
    (x y : LaurentSeries F) :
    coefficientDerivation ξ (starProduct p hp δ η x y) =
      starProduct p hp δ η (coefficientDerivation ξ x) y +
        starProduct p hp δ η x (coefficientDerivation ξ y) := by
  ext n
  simp only [coefficientDerivation_coeff, starProduct_coeff, coeff_add]
  change ξ.toLinearMap (∑ᶠ j, (starTerm p δ η x y j).coeff n) = _
  rw [map_finsum ξ.toLinearMap (f := fun j ↦ (starTerm p δ η x y j).coeff n)
    ((starFamily p hp δ η x y).finite_co_support n)]
  have heq (j : ℕ) : ξ.toLinearMap ((starTerm p δ η x y j).coeff n) =
      (starTerm p δ η (coefficientDerivation ξ x) y j).coeff n +
        (starTerm p δ η x (coefficientDerivation ξ y) j).coeff n := by
    change (coefficientDerivation ξ (starTerm p δ η x y j)).coeff n = _
    rw [coefficientDerivation_starTerm p δ η ξ hδ hη, coeff_add]
  simp only [heq]
  exact finsum_add_distrib
    ((starFamily p hp δ η (coefficientDerivation ξ x) y).finite_co_support n)
    ((starFamily p hp δ η x (coefficientDerivation ξ y)).finite_co_support n)

theorem starProduct_eq_mul_of_delta_eq_zero (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (x y : LaurentSeries F) (hx : deltaOperator p η x = 0) :
    starProduct p hp δ η x y = x * y := by
  ext n
  rw [starProduct_coeff, finsum_eq_single _ 0]
  · simp
  · intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [starTerm, Function.iterate_succ_apply, hx]

theorem starProduct_eq_mul_of_coefficientDerivation_eq_zero (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (x y : LaurentSeries F)
    (hy : coefficientDerivation δ y = 0) : starProduct p hp δ η x y = x * y := by
  ext n
  rw [starProduct_coeff, finsum_eq_single _ 0]
  · simp
  · intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [starTerm, Function.iterate_succ_apply, hy]

/-- Elements killed by both defining derivations multiply centrally and ordinarily. -/
theorem starProduct_central (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (c x : LaurentSeries F) (hΔ : deltaOperator p η c = 0)
    (hδ : coefficientDerivation δ c = 0) :
    starProduct p hp δ η c x = c * x ∧ starProduct p hp δ η x c = c * x := by
  constructor
  · exact starProduct_eq_mul_of_delta_eq_zero p hp δ η c x hΔ
  · rw [starProduct_eq_mul_of_coefficientDerivation_eq_zero p hp δ η x c hδ, mul_comm]

/-- Such a nonzero central element has its ordinary Laurent inverse as a star inverse. -/
theorem starProduct_central_inverse (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (c : LaurentSeries F) (hc : c ≠ 0) (hΔ : deltaOperator p η c = 0)
    (hδ : coefficientDerivation δ c = 0) :
    starProduct p hp δ η c c⁻¹ = 1 ∧ starProduct p hp δ η c⁻¹ c = 1 := by
  rw [starProduct_eq_mul_of_delta_eq_zero p hp δ η c c⁻¹ hΔ,
    starProduct_eq_mul_of_coefficientDerivation_eq_zero p hp δ η c⁻¹ c hδ,
    mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
  exact ⟨rfl, rfl⟩

/-- The coefficient hypotheses for the central monomial twist in the paper. -/
theorem monomial_twist_killed (p : ℕ) (δ η : Derivation k F F) (n : ℤ) (a : F)
    (hδ : δ a = 0) (hη : η a = (p : F)⁻¹ * (n : F) * a) :
    deltaOperator p η (single n a) = 0 ∧ coefficientDerivation δ (single n a) = 0 := by
  simp [deltaOperator_single, hη, hδ]

/-- The finite iterated Leibniz expansion needed in the star-associativity calculation. -/
theorem derivation_iterate_mul (D : Derivation k (LaurentSeries F) (LaurentSeries F))
    (j : ℕ) (x y : LaurentSeries F) :
    D^[j] (x * y) = ∑ ab ∈ Finset.antidiagonal j,
      j.choose ab.1 • (D^[ab.1] x * D^[ab.2] y) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun a b ↦ D^[a] x * D^[b] y) j]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, smul_add, sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro ab hab
    rw [j.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hab).symm]
    ring

section SummableOperators

variable {ι : Type*}

/-- Applying a coefficient derivation preserves summability. -/
def coefficientFamily (δ : Derivation k F F) (s : SummableFamily ℤ F ι) :
    SummableFamily ℤ F ι where
  toFun i := coefficientDerivation δ (s i)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono <| Set.iUnion_mono fun i ↦
    coefficientMap_support_subset δ (s i)
  finite_co_support' n := (s.finite_co_support n).subset <| by
    intro i hi
    change δ ((s i).coeff n) ≠ 0 at hi
    exact fun h ↦ hi (by simp [h])

@[simp] theorem coefficientFamily_apply (δ : Derivation k F F)
    (s : SummableFamily ℤ F ι) (i : ι) :
    coefficientFamily δ s i = coefficientDerivation δ (s i) := rfl

theorem coefficientFamily_hsum (δ : Derivation k F F) (s : SummableFamily ℤ F ι) :
    (coefficientFamily δ s).hsum = coefficientDerivation δ s.hsum := by
  ext n
  exact (map_finsum δ.toLinearMap (s.finite_co_support n)).symm

/-- Applying Δ preserves summability, since its output support shifts by `p`. -/
def deltaFamily (p : ℕ) (η : Derivation k F F) (s : SummableFamily ℤ F ι) :
    SummableFamily ℤ F ι where
  toFun i := deltaOperator p η (s i)
  isPWO_iUnion_support' := by
    let t : SummableFamily ℤ F ι := (single (p : ℤ) (1 : F)) • s
    apply t.isPWO_iUnion_support.mono
    apply Set.iUnion_mono
    intro i n hn
    change (deltaOperator p η (s i)).coeff n ≠ 0 at hn
    change (((single (p : ℤ) (1 : F)) * s i)).coeff n ≠ 0
    rw [coeff_single_mul, one_mul]
    exact fun h ↦ hn (by simp [h])
  finite_co_support' n := (s.finite_co_support (n - p)).subset <| by
    intro i hi
    change (deltaOperator p η (s i)).coeff n ≠ 0 at hi
    exact fun h ↦ hi (by simp [h])

@[simp] theorem deltaFamily_apply (p : ℕ) (η : Derivation k F F)
    (s : SummableFamily ℤ F ι) (i : ι) : deltaFamily p η s i = deltaOperator p η (s i) := rfl

theorem deltaFamily_hsum (p : ℕ) (η : Derivation k F F) (s : SummableFamily ℤ F ι) :
    (deltaFamily p η s).hsum = deltaOperator p η s.hsum := by
  ext n
  let L : F →ₗ[k] F := η.toLinearMap -
    ((p : F)⁻¹ * ((n - p : ℤ) : F)) • LinearMap.id
  simpa only [SummableFamily.coeff_hsum, deltaFamily_apply, deltaOperator_coeff,
    L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    mul_assoc] using (map_finsum L (s.finite_co_support (n - p))).symm

theorem deltaFamily_iterate_apply (p : ℕ) (η : Derivation k F F)
    (s : SummableFamily ℤ F ι) (j : ℕ) (i : ι) :
    ((deltaFamily p η)^[j] s) i = (deltaOperator p η)^[j] (s i) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Function.iterate_succ_apply', ih]

theorem deltaFamily_iterate_hsum (p : ℕ) (η : Derivation k F F)
    (s : SummableFamily ℤ F ι) (j : ℕ) :
    ((deltaFamily p η)^[j] s).hsum = (deltaOperator p η)^[j] s.hsum := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Function.iterate_succ_apply', deltaFamily_hsum, ih]

end SummableOperators

/-- The two factorial denominators produced by splitting an iterated derivative. -/
theorem inverse_factorial_mul_choose [CharZero F] (a b : ℕ) :
    ((a + b).factorial : F)⁻¹ * ((a + b).choose a : F) =
      (a.factorial : F)⁻¹ * (b.factorial : F)⁻¹ := by
  have ha : (a.factorial : F) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : F) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hab : ((a + b).factorial : F) ≠ 0 := by exact_mod_cast (a + b).factorial_ne_zero
  have h : (((a + b).choose a : F) * a.factorial) * b.factorial = (a + b).factorial := by
    rw [Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial a b
  field_simp
  linear_combination h

/-- A finite-index-degree criterion for coefficientwise summability. -/
def summableOfDegree {ι : Type*} (f : ι → LaurentSeries F) (w : ι → ℕ)
    (hw : ∀ N : ℕ, {i | w i ≤ N}.Finite) (b : ℤ)
    (hf : ∀ i, LowerBound (b + w i) (f i)) : SummableFamily ℤ F ι where
  toFun := f
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨b, ?_⟩
    intro n hn
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
    by_contra! hnb
    exact hi (hf i n (by omega))
  finite_co_support' n := (hw (n - b).toNat).subset <| by
    intro i hi
    have hni : b + w i ≤ n := by
      by_contra! h
      exact hi (hf i n h)
    change w i ≤ (n - b).toNat
    omega

/-- The common triple term in the formal associativity expansion. -/
def associativityTerm (p : ℕ) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) (abc : ℕ × ℕ × ℕ) : LaurentSeries F :=
  ((abc.1.factorial : F)⁻¹ * (abc.2.1.factorial : F)⁻¹ * (abc.2.2.factorial : F)⁻¹) •
    (((deltaOperator p η)^[abc.1 + abc.2.1] x) *
      ((deltaOperator p η)^[abc.2.2] ((coefficientDerivation δ)^[abc.1] y)) *
        ((coefficientDerivation δ)^[abc.2.1 + abc.2.2] z))

theorem associativityTerm_lowerBound (p : ℕ) (δ η : Derivation k F F)
    {x y z : LaurentSeries F} {b c d : ℤ}
    (hx : LowerBound b x) (hy : LowerBound c y) (hz : LowerBound d z)
    (abc : ℕ × ℕ × ℕ) :
    LowerBound (b + c + d + (p : ℤ) * (abc.1 + abc.2.1 + abc.2.2))
      (associativityTerm p δ η x y z abc) := by
  have h := (((hx.deltaOperator_iterate p η (abc.1 + abc.2.1)).mul
    ((hy.coefficientDerivation_iterate δ abc.1).deltaOperator_iterate p η abc.2.2)).mul
      (hz.coefficientDerivation_iterate δ (abc.2.1 + abc.2.2))).smul
        ((abc.1.factorial : F)⁻¹ * (abc.2.1.factorial : F)⁻¹ * (abc.2.2.factorial : F)⁻¹)
  convert h using 1
  push_cast
  ring

/-- The triple sum used for associativity is genuinely locally finite. -/
def associativityFamily (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) : SummableFamily ℤ F (ℕ × ℕ × ℕ) :=
  summableOfDegree (associativityTerm p δ η x y z) (fun abc ↦ abc.1 + abc.2.1 + abc.2.2)
    (fun N ↦ ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod (Set.finite_Iic N))).subset
      (by
        intro abc habc
        change abc.1 ≤ N ∧ abc.2.1 ≤ N ∧ abc.2.2 ≤ N
        dsimp at habc
        omega))
    (x.order + y.order + z.order) fun abc ↦
      (associativityTerm_lowerBound p δ η
        (lowerBound_order x) (lowerBound_order y) (lowerBound_order z) abc).mono (by
          push_cast
          have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
          have ha : (0 : ℤ) ≤ abc.1 := by omega
          have hb : (0 : ℤ) ≤ abc.2.1 := by omega
          have hc : (0 : ℤ) ≤ abc.2.2 := by omega
          nlinarith)

theorem deltaOperator_smul_of_eq_zero (p : ℕ) (η : Derivation k F F) (a : F)
    (ha : η a = 0) (x : LaurentSeries F) :
    deltaOperator p η (a • x) = a • deltaOperator p η x := by
  ext n
  simp [coeff_smul, smul_eq_mul, Derivation.leibniz, ha]
  ring

theorem deltaOperator_iterate_smul_of_eq_zero (p : ℕ) (η : Derivation k F F) (a : F)
    (ha : η a = 0) (j : ℕ) (x : LaurentSeries F) :
    (deltaOperator p η)^[j] (a • x) = a • (deltaOperator p η)^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ih, deltaOperator_smul_of_eq_zero p η a ha]

theorem coefficientDerivation_iterate_smul_of_eq_zero (δ : Derivation k F F) (a : F)
    (ha : δ a = 0) (j : ℕ) (x : LaurentSeries F) :
    (coefficientDerivation δ)^[j] (a • x) = a • (coefficientDerivation δ)^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ih, coefficientDerivation_smul_of_eq_zero δ a ha]

/-- The finite expansion of one outer term of the left-associated star product. -/
theorem starTerm_starTerm_left [CharZero F] (p : ℕ) (δ η : Derivation k F F)
    (x y z : LaurentSeries F) (i j : ℕ) :
    starTerm p δ η (starTerm p δ η x y i) z j =
      ∑ ab ∈ Finset.antidiagonal j, associativityTerm p δ η x y z (i, ab.1, ab.2) := by
  have hi : η ((i.factorial : F)⁻¹) = 0 := by rw [Derivation.leibniz_inv]; simp
  simp only [starTerm, deltaOperator_iterate_smul_of_eq_zero p η _ hi,
    derivation_iterate_mul, smul_sum, sum_mul]
  apply sum_congr rfl
  intro ab hab
  obtain ⟨a, b⟩ := ab
  have hab' : a + b = j := Finset.mem_antidiagonal.mp hab
  subst j
  simp only [associativityTerm, ← Nat.cast_smul_eq_nsmul F, smul_mul_assoc, smul_smul,
    ← Function.iterate_add_apply, Nat.add_comm a i]
  rw [show ((a + b).factorial : F)⁻¹ *
      ((i.factorial : F)⁻¹ * ((a + b).choose a : F)) =
      (i.factorial : F)⁻¹ * ((a.factorial : F)⁻¹ * (b.factorial : F)⁻¹) by
    rw [mul_left_comm, inverse_factorial_mul_choose]]
  simp only [mul_assoc]

/-- The finite expansion of one outer term of the right-associated star product. -/
theorem starTerm_starTerm_right [CharZero F] (p : ℕ) (δ η : Derivation k F F)
    (h : Function.Commute δ η) (x y z : LaurentSeries F) (i j : ℕ) :
    starTerm p δ η x (starTerm p δ η y z j) i =
      ∑ ab ∈ Finset.antidiagonal i, associativityTerm p δ η x y z (ab.1, ab.2, j) := by
  have hj : δ ((j.factorial : F)⁻¹) = 0 := by rw [Derivation.leibniz_inv]; simp
  simp only [starTerm, coefficientDerivation_iterate_smul_of_eq_zero δ _ hj,
    derivation_iterate_mul, smul_sum, mul_sum]
  apply sum_congr rfl
  intro ab hab
  obtain ⟨a, b⟩ := ab
  have hab' : a + b = i := Finset.mem_antidiagonal.mp hab
  subst i
  have hcomm := ((coefficientDerivation_delta_commute p δ η h).iterate_right j).iterate_left a
  simp only [associativityTerm, ← Nat.cast_smul_eq_nsmul F, mul_smul_comm, smul_smul,
    ← Function.iterate_add_apply, hcomm y]
  rw [show ((a + b).factorial : F)⁻¹ *
      ((j.factorial : F)⁻¹ * ((a + b).choose a : F)) =
      (a.factorial : F)⁻¹ * (b.factorial : F)⁻¹ * (j.factorial : F)⁻¹ by
    rw [mul_left_comm, inverse_factorial_mul_choose]; ring]
  simp only [mul_assoc]

section SummableTerm

variable {ι : Type*}

theorem coefficientFamily_iterate_apply (δ : Derivation k F F)
    (s : SummableFamily ℤ F ι) (j : ℕ) (i : ι) :
    ((coefficientFamily δ)^[j] s) i = (coefficientDerivation δ)^[j] (s i) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Function.iterate_succ_apply', ih]

theorem coefficientFamily_iterate_hsum (δ : Derivation k F F)
    (s : SummableFamily ℤ F ι) (j : ℕ) :
    ((coefficientFamily δ)^[j] s).hsum = (coefficientDerivation δ)^[j] s.hsum := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Function.iterate_succ_apply', coefficientFamily_hsum, ih]

theorem starTerm_hsum_left_coeff (p : ℕ) (δ η : Derivation k F F)
    (s : SummableFamily ℤ F ι) (z : LaurentSeries F) (j : ℕ) (n : ℤ) :
    (starTerm p δ η s.hsum z j).coeff n =
      ∑ᶠ i, (starTerm p δ η (s i) z j).coeff n := by
  let A : LaurentSeries F := (j.factorial : F)⁻¹ • (coefficientDerivation δ)^[j] z
  have heq (v : LaurentSeries F) : starTerm p δ η v z j = A * (deltaOperator p η)^[j] v := by
    simp only [A, starTerm, smul_mul_assoc, mul_comm]
  simp only [heq]
  rw [← deltaFamily_iterate_hsum p η s j, ← SummableFamily.hsum_smul]
  apply finsum_congr
  intro i
  change (A * ((deltaFamily p η)^[j] s) i).coeff n = _
  rw [deltaFamily_iterate_apply]

theorem starTerm_hsum_right_coeff (p : ℕ) (δ η : Derivation k F F)
    (s : SummableFamily ℤ F ι) (x : LaurentSeries F) (j : ℕ) (n : ℤ) :
    (starTerm p δ η x s.hsum j).coeff n =
      ∑ᶠ i, (starTerm p δ η x (s i) j).coeff n := by
  let A : LaurentSeries F := (j.factorial : F)⁻¹ • (deltaOperator p η)^[j] x
  have heq (v : LaurentSeries F) : starTerm p δ η x v j =
      A * (coefficientDerivation δ)^[j] v := by
    simp only [A, starTerm, smul_mul_assoc]
  simp only [heq]
  rw [← coefficientFamily_iterate_hsum δ s j, ← SummableFamily.hsum_smul]
  apply finsum_congr
  intro i
  change (A * ((coefficientFamily δ)^[j] s) i).coeff n = _
  rw [coefficientFamily_iterate_apply]

end SummableTerm

private theorem finsum_antidiagonal (f : ℕ × ℕ → F) (hf : Function.HasFiniteSupport f) :
    (∑ᶠ n, ∑ ab ∈ Finset.antidiagonal n, f ab) = ∑ᶠ ab, f ab := by
  classical
  let s := hf.toFinset
  have hs (ab : ℕ × ℕ) : ab ∈ s ↔ f ab ≠ 0 := by
    simp [s, Function.mem_support]
  have hinner (n : ℕ) : (∑ ab ∈ Finset.antidiagonal n, f ab) =
      ∑ ab ∈ s.filter (fun ab ↦ ab.1 + ab.2 = n), f ab := by
    symm
    apply sum_subset
    · intro ab hab
      exact Finset.mem_antidiagonal.mpr (mem_filter.mp hab).2
    · intro ab hab hnot
      by_contra! hnonzero
      exact hnot (mem_filter.mpr ⟨(hs ab).mpr hnonzero, Finset.mem_antidiagonal.mp hab⟩)
  have houter : Function.support (fun n ↦ ∑ ab ∈ Finset.antidiagonal n, f ab) ⊆
      ↑(s.image (fun ab ↦ ab.1 + ab.2)) := by
    intro n hn
    obtain ⟨ab, hab, hnz⟩ := exists_ne_zero_of_sum_ne_zero hn
    exact mem_image.mpr ⟨ab, (hs ab).mpr hnz, Finset.mem_antidiagonal.mp hab⟩
  rw [finsum_eq_sum_of_support_subset _ houter, finsum_eq_sum _ hf]
  simp only [hinner]
  exact sum_fiberwise_of_maps_to (fun ab hab ↦ mem_image_of_mem _ hab) f

private theorem finsum_pair_comm (f : ℕ × ℕ → F) (hf : Function.HasFiniteSupport f) :
    (∑ᶠ a, ∑ᶠ b, f (a, b)) = ∑ᶠ b, ∑ᶠ a, f (a, b) := by
  rw [← finsum_curry f hf]
  have hs := hf.fun_comp_of_injective (Equiv.prodComm ℕ ℕ).injective
  rw [← finsum_curry (fun ab ↦ f (ab.2, ab.1)) hs]
  exact finsum_eq_of_bijective (Equiv.prodComm ℕ ℕ)
    (Equiv.prodComm ℕ ℕ).bijective (fun _ ↦ rfl)

private theorem finsum_triple_group (f : ℕ × ℕ × ℕ → F)
    (hf : Function.HasFiniteSupport f) :
    (∑ᶠ n, ∑ᶠ i, ∑ ab ∈ Finset.antidiagonal n, f (i, ab.1, ab.2)) =
      ∑ᶠ abc, f abc := by
  have hg : Function.HasFiniteSupport
      (fun ni : ℕ × ℕ ↦ ∑ ab ∈ Finset.antidiagonal ni.1, f (ni.2, ab.1, ab.2)) := by
    refine (hf.image (fun abc ↦ (abc.2.1 + abc.2.2, abc.1))).subset ?_
    intro ni hni
    obtain ⟨ab, hab, hnz⟩ := exists_ne_zero_of_sum_ne_zero hni
    refine ⟨(ni.2, ab.1, ab.2), hnz, ?_⟩
    simp [Finset.mem_antidiagonal.mp hab]
  rw [finsum_pair_comm _ hg]
  have heq (i : ℕ) : (∑ᶠ n, ∑ ab ∈ Finset.antidiagonal n, f (i, ab.1, ab.2)) =
      ∑ᶠ ab : ℕ × ℕ, f (i, ab.1, ab.2) := by
    apply finsum_antidiagonal
    exact hf.fun_comp_of_injective (fun a b hab ↦ (Prod.mk.inj hab).2)
  simp only [heq]
  exact (finsum_curry f hf).symm

/-- Associativity of the actual locally finite star product for commuting field derivations. -/
theorem starProduct_assoc [CharZero F] (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (h : Function.Commute δ η) (x y z : LaurentSeries F) :
    starProduct p hp δ η (starProduct p hp δ η x y) z =
      starProduct p hp δ η x (starProduct p hp δ η y z) := by
  ext n
  let f : ℕ × ℕ × ℕ → F := fun abc ↦ (associativityTerm p δ η x y z abc).coeff n
  have hf : Function.HasFiniteSupport f :=
    (associativityFamily p hp δ η x y z).finite_co_support n
  have hleft : (starProduct p hp δ η (starProduct p hp δ η x y) z).coeff n =
      ∑ᶠ abc, f abc := by
    rw [starProduct_coeff]
    calc
      _ = ∑ᶠ j, ∑ᶠ i, (starTerm p δ η (starTerm p δ η x y i) z j).coeff n := by
        apply finsum_congr
        intro j
        exact starTerm_hsum_left_coeff p δ η (starFamily p hp δ η x y) z j n
      _ = ∑ᶠ j, ∑ᶠ i, ∑ ab ∈ Finset.antidiagonal j, f (i, ab.1, ab.2) := by
        apply finsum_congr
        intro j
        apply finsum_congr
        intro i
        rw [starTerm_starTerm_left, coeff_sum]
      _ = _ := finsum_triple_group f hf
  let e : (ℕ × ℕ × ℕ) ≃ (ℕ × ℕ × ℕ) :=
    { toFun := fun abc ↦ (abc.2.1, abc.2.2, abc.1)
      invFun := fun abc ↦ (abc.2.2, abc.1, abc.2.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfe : Function.HasFiniteSupport (fun abc ↦ f (e abc)) :=
    hf.fun_comp_of_injective e.injective
  rw [hleft, starProduct_coeff]
  symm
  calc
    _ = ∑ᶠ i, ∑ᶠ j, (starTerm p δ η x (starTerm p δ η y z j) i).coeff n := by
      apply finsum_congr
      intro i
      exact starTerm_hsum_right_coeff p δ η (starFamily p hp δ η y z) x i n
    _ = ∑ᶠ i, ∑ᶠ j, ∑ ab ∈ Finset.antidiagonal i, f (e (j, ab.1, ab.2)) := by
      apply finsum_congr
      intro i
      apply finsum_congr
      intro j
      rw [starTerm_starTerm_right p δ η h, coeff_sum]
      rfl
    _ = ∑ᶠ abc, f (e abc) := finsum_triple_group (fun abc ↦ f (e abc)) hfe
    _ = ∑ᶠ abc, f abc := finsum_eq_of_bijective e e.bijective (fun _ ↦ rfl)

/-- The distinct type carrying star multiplication. The underlying Laurent ring is unchanged. -/
def StarSeries (p : ℕ) (_hp : 0 < p) (δ η : Derivation k F F)
    (_h : Function.Commute δ η) : Type _ := LaurentSeries F

namespace StarSeries

variable {p : ℕ} {hp : 0 < p} {δ η : Derivation k F F}
variable {h : Function.Commute δ η}

/-- Forget the star multiplication, retaining the coefficient sequence. -/
def toSeries (x : StarSeries p hp δ η h) : LaurentSeries F := x

/-- Regard an ordinary Laurent series as an element of the star algebra. -/
def ofSeries (x : LaurentSeries F) : StarSeries p hp δ η h := x

@[simp] theorem toSeries_ofSeries (x : LaurentSeries F) :
    toSeries (ofSeries (hp := hp) (h := h) x) = x := rfl

@[simp] theorem ofSeries_toSeries (x : StarSeries p hp δ η h) :
    ofSeries (toSeries x) = x := rfl

variable [CharZero F]

instance : Ring (StarSeries p hp δ η h) where
  __ := (inferInstance : AddCommGroup (LaurentSeries F))
  __ := (inferInstance : AddGroupWithOne (LaurentSeries F))
  mul := starProduct p hp δ η
  mul_assoc := starProduct_assoc p hp δ η h
  one_mul := starProduct_one_left p hp δ η
  mul_one := starProduct_one_right p hp δ η
  zero_mul := starProduct_zero_left p hp δ η
  mul_zero := starProduct_zero_right p hp δ η
  left_distrib := starProduct_add_right p hp δ η
  right_distrib := starProduct_add_left p hp δ η

@[simp] theorem toSeries_zero : toSeries (0 : StarSeries p hp δ η h) = 0 := rfl
@[simp] theorem toSeries_one : toSeries (1 : StarSeries p hp δ η h) = 1 := rfl
@[simp] theorem toSeries_add (x y : StarSeries p hp δ η h) :
    toSeries (x + y) = toSeries x + toSeries y := rfl
@[simp] theorem toSeries_neg (x : StarSeries p hp δ η h) :
    toSeries (-x) = -toSeries x := rfl
@[simp] theorem toSeries_mul (x y : StarSeries p hp δ η h) :
    toSeries (x * y) = starProduct p hp δ η (toSeries x) (toSeries y) := rfl

/-- The central copy of the original base field in the star algebra. -/
def constants : k →+* StarSeries p hp δ η h where
  toFun a := ofSeries (single 0 (algebraMap k F a))
  map_zero' := by change (single 0 (algebraMap k F 0) : LaurentSeries F) = 0; simp
  map_one' := by change (single 0 (algebraMap k F 1) : LaurentSeries F) = 1; simp
  map_add' a b := by
    change (single 0 (algebraMap k F (a + b)) : LaurentSeries F) =
      single 0 (algebraMap k F a) + single 0 (algebraMap k F b)
    simp
    rfl
  map_mul' a b := by
    change (single 0 (algebraMap k F (a * b)) : LaurentSeries F) =
      starProduct p hp δ η (single 0 (algebraMap k F a)) (single 0 (algebraMap k F b))
    rw [starProduct_eq_mul_of_delta_eq_zero p hp δ η _ _ (by simp [deltaOperator_single])]
    simp [single_mul_single]

instance : Algebra k (StarSeries p hp δ η h) where
  smul a x := ofSeries (a • toSeries x)
  algebraMap := constants
  commutes' a x := by
    change starProduct p hp δ η (single 0 (algebraMap k F a)) (toSeries x) =
      starProduct p hp δ η (toSeries x) (single 0 (algebraMap k F a))
    rw [starProduct_eq_mul_of_delta_eq_zero p hp δ η _ _ (by simp [deltaOperator_single]),
      starProduct_eq_mul_of_coefficientDerivation_eq_zero p hp δ η _ _ (by simp), mul_comm]
  smul_def' a x := by
    change a • toSeries x = starProduct p hp δ η (single 0 (algebraMap k F a)) (toSeries x)
    rw [starProduct_eq_mul_of_delta_eq_zero p hp δ η _ _ (by simp [deltaOperator_single])]
    rw [Algebra.smul_def]
    rfl

@[simp] theorem toSeries_algebraMap (a : k) :
    toSeries (algebraMap k (StarSeries p hp δ η h) a) = single 0 (algebraMap k F a) := rfl

@[simp] theorem toSeries_smul (a : k) (x : StarSeries p hp δ η h) :
    toSeries (a • x) = a • toSeries x := rfl

instance : Nontrivial (StarSeries p hp δ η h) :=
  inferInstanceAs (Nontrivial (LaurentSeries F))

/-- Free-polynomial evaluation in the actual associative star algebra. -/
def evaluate {ι : Type*} (v : ι → StarSeries p hp δ η h) :
    FreeAlgebra k ι →ₐ[k] StarSeries p hp δ η h := FreeAlgebra.lift k v

@[simp] theorem evaluate_generator {ι : Type*} (v : ι → StarSeries p hp δ η h) (i : ι) :
    evaluate v (FreeAlgebra.ι k i) = v i := by simp [evaluate]

/-- Evaluate the false/true generators at the first/second specified series. -/
def evaluatePair (x y : LaurentSeries F) :
    FreeAlgebra k Bool →ₐ[k] StarSeries p hp δ η h :=
  evaluate (fun b ↦ ofSeries (if b then y else x))

@[simp] theorem evaluatePair_false (x y : LaurentSeries F) :
    toSeries (evaluatePair (hp := hp) (h := h) x y (FreeAlgebra.ι k false)) = x := by
  simp [evaluatePair]

@[simp] theorem evaluatePair_true (x y : LaurentSeries F) :
    toSeries (evaluatePair (hp := hp) (h := h) x y (FreeAlgebra.ι k true)) = y := by
  simp [evaluatePair]

theorem evaluatePair_mul (x y : LaurentSeries F) (f g : FreeAlgebra k Bool) :
    toSeries (evaluatePair (hp := hp) (h := h) x y (f * g)) =
      starProduct p hp δ η (toSeries (evaluatePair (hp := hp) (h := h) x y f))
        (toSeries (evaluatePair (hp := hp) (h := h) x y g)) := by
  rw [map_mul, toSeries_mul]

/-- The evaluation `f(D,Z)` used by the Newton construction in the submitted proof. -/
def evaluateAt (z : LaurentSeries F) :
    FreeAlgebra k Bool →ₐ[k] StarSeries p hp δ η h := evaluatePair (distinguishedSymbol p) z

@[simp] theorem evaluateAt_false (z : LaurentSeries F) :
    toSeries (evaluateAt (hp := hp) (h := h) z (FreeAlgebra.ι k false)) =
      distinguishedSymbol p := by
  simp [evaluateAt]

@[simp] theorem evaluateAt_true (z : LaurentSeries F) :
    toSeries (evaluateAt (hp := hp) (h := h) z (FreeAlgebra.ι k true)) = z := by
  simp [evaluateAt]

end StarSeries

section FieldExtension

variable {G : Type*} [Field G] [Algebra k G]

/-- Extend the coefficient field of an ordinary Laurent series. -/
def mapField (φ : F →ₐ[k] G) (x : LaurentSeries F) : LaurentSeries G :=
  x.map φ.toRingHom

@[simp] theorem mapField_coeff (φ : F →ₐ[k] G) (x : LaurentSeries F) (n : ℤ) :
    (mapField φ x).coeff n = φ (x.coeff n) := rfl

theorem mapField_injective (φ : F →ₐ[k] G) : Function.Injective (mapField φ) := by
  intro x y h
  ext n
  apply φ.injective
  exact congrArg (fun z ↦ z.coeff n) h

@[simp] theorem mapField_zero (φ : F →ₐ[k] G) : mapField φ 0 = 0 := by ext; simp
@[simp] theorem mapField_one (φ : F →ₐ[k] G) : mapField φ 1 = 1 := by
  ext n
  by_cases hn : n = 0 <;> simp [hn]

@[simp] theorem mapField_add (φ : F →ₐ[k] G) (x y : LaurentSeries F) :
    mapField φ (x + y) = mapField φ x + mapField φ y := by ext; simp

@[simp] theorem mapField_mul (φ : F →ₐ[k] G) (x y : LaurentSeries F) :
    mapField φ (x * y) = mapField φ x * mapField φ y :=
  HahnSeries.map_mul φ.toRingHom.toNonUnitalRingHom

@[simp] theorem mapField_smul (φ : F →ₐ[k] G) (a : F) (x : LaurentSeries F) :
    mapField φ (a • x) = φ a • mapField φ x := by
  ext n
  simp [coeff_smul, smul_eq_mul]

@[simp] theorem mapField_single (φ : F →ₐ[k] G) (n : ℤ) (a : F) :
    mapField φ (single n a) = single n (φ a) := by
  ext m
  by_cases hm : m = n <;> simp [hm]

theorem mapField_coefficientDerivation (φ : F →ₐ[k] G)
    (δ : Derivation k F F) (δ' : Derivation k G G)
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (x : LaurentSeries F) :
    mapField φ (coefficientDerivation δ x) = coefficientDerivation δ' (mapField φ x) := by
  ext n
  exact hδ (x.coeff n)

theorem mapField_deltaOperator (φ : F →ₐ[k] G) (p : ℕ)
    (η : Derivation k F F) (η' : Derivation k G G)
    (hη : ∀ a, φ (η a) = η' (φ a)) (x : LaurentSeries F) :
    mapField φ (deltaOperator p η x) = deltaOperator p η' (mapField φ x) := by
  ext n
  simp [hη]

theorem mapField_starTerm (φ : F →ₐ[k] G) (p : ℕ)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (x y : LaurentSeries F) (j : ℕ) :
    mapField φ (starTerm p δ η x y j) =
      starTerm p δ' η' (mapField φ x) (mapField φ y) j := by
  have hΔ : Function.Semiconj (mapField φ) (deltaOperator p η) (deltaOperator p η') :=
    mapField_deltaOperator φ p η η' hη
  have hD : Function.Semiconj (mapField φ)
      (coefficientDerivation δ) (coefficientDerivation δ') :=
    mapField_coefficientDerivation φ δ δ' hδ
  simp [starTerm, hΔ.iterate_right j x, hD.iterate_right j y]

/-- Differential coefficient-field maps preserve the infinite star product. -/
theorem mapField_starProduct (φ : F →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a))
    (x y : LaurentSeries F) :
    mapField φ (starProduct p hp δ η x y) =
      starProduct p hp δ' η' (mapField φ x) (mapField φ y) := by
  ext n
  simp only [mapField_coeff, starProduct_coeff]
  change φ.toLinearMap (∑ᶠ j, (starTerm p δ η x y j).coeff n) = _
  rw [map_finsum φ.toLinearMap (f := fun j ↦ (starTerm p δ η x y j).coeff n)
    ((starFamily p hp δ η x y).finite_co_support n)]
  apply finsum_congr
  intro j
  exact congrArg (fun z ↦ z.coeff n) (mapField_starTerm φ p δ η δ' η' hδ hη x y j)

theorem lowerBound_mapField_iff (φ : F →ₐ[k] G) (b : ℤ) (x : LaurentSeries F) :
    LowerBound b (mapField φ x) ↔ LowerBound b x := by
  constructor
  · intro h n hn
    apply φ.injective
    simpa using h n hn
  · intro h n hn
    simp [h n hn]

/-- The induced algebra homomorphism between actual star algebras. -/
def mapFieldAlgHom [CharZero F] [CharZero G] (φ : F →ₐ[k] G) (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (δ' η' : Derivation k G G)
    (h : Function.Commute δ η) (h' : Function.Commute δ' η')
    (hδ : ∀ a, φ (δ a) = δ' (φ a)) (hη : ∀ a, φ (η a) = η' (φ a)) :
    StarSeries p hp δ η h →ₐ[k] StarSeries p hp δ' η' h' where
  toFun x := StarSeries.ofSeries (mapField φ (StarSeries.toSeries x))
  map_zero' := mapField_zero φ
  map_one' := mapField_one φ
  map_add' := mapField_add φ
  map_mul' := mapField_starProduct φ p hp δ η δ' η' hδ hη
  commutes' a := by
    change mapField φ (single 0 (algebraMap k F a)) = single 0 (algebraMap k G a)
    simp

end FieldExtension

section LatticeRefinement

/-- The index embedding corresponding to replacing denominator p by p·e. -/
def latticeIndex (e : ℕ) (he : 0 < e) : ℤ ↪o ℤ where
  toFun n := (e : ℤ) * n
  inj' a b hab := by
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    nlinarith
  map_rel_iff' := by
    intro a b
    change (e : ℤ) * a ≤ (e : ℤ) * b ↔ a ≤ b
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    constructor <;> intro h <;> nlinarith

/-- Refine the exponent lattice without changing the represented rational exponents. -/
def refineLattice (e : ℕ) (he : 0 < e) (x : LaurentSeries F) : LaurentSeries F :=
  HahnSeries.embDomain (latticeIndex e he) x

@[simp] theorem refineLattice_coeff (e : ℕ) (he : 0 < e) (x : LaurentSeries F) (n : ℤ) :
    (refineLattice e he x).coeff ((e : ℤ) * n) = x.coeff n :=
  HahnSeries.embDomain_coeff

theorem refineLattice_coeff_off (e : ℕ) (he : 0 < e) (x : LaurentSeries F) (n : ℤ)
    (hn : ¬ ∃ m : ℤ, (e : ℤ) * m = n) : (refineLattice e he x).coeff n = 0 :=
  HahnSeries.embDomain_notin_range hn

theorem refineLattice_injective (e : ℕ) (he : 0 < e) :
    Function.Injective (refineLattice (F := F) e he) := HahnSeries.embDomain_injective

@[simp] theorem refineLattice_zero (e : ℕ) (he : 0 < e) :
    refineLattice (F := F) e he 0 = 0 := HahnSeries.embDomain_zero

@[simp] theorem refineLattice_one (e : ℕ) (he : 0 < e) :
    refineLattice (F := F) e he 1 = 1 := HahnSeries.embDomain_one _ (by simp [latticeIndex])

@[simp] theorem refineLattice_add (e : ℕ) (he : 0 < e) (x y : LaurentSeries F) :
    refineLattice e he (x + y) = refineLattice e he x + refineLattice e he y :=
  HahnSeries.embDomain_add _ x y

@[simp] theorem refineLattice_mul (e : ℕ) (he : 0 < e) (x y : LaurentSeries F) :
    refineLattice e he (x * y) = refineLattice e he x * refineLattice e he y :=
  HahnSeries.embDomain_mul _ (fun a b ↦ mul_add _ a b) x y

@[simp] theorem refineLattice_smul (e : ℕ) (he : 0 < e) (a : F) (x : LaurentSeries F) :
    refineLattice e he (a • x) = a • refineLattice e he x := HahnSeries.embDomain_smul _ a x

@[simp] theorem refineLattice_single (e : ℕ) (he : 0 < e) (n : ℤ) (a : F) :
    refineLattice e he (single n a) = single ((e : ℤ) * n) a := HahnSeries.embDomain_single

theorem refineLattice_coefficientDerivation (e : ℕ) (he : 0 < e)
    (δ : Derivation k F F) (x : LaurentSeries F) :
    refineLattice e he (coefficientDerivation δ x) =
      coefficientDerivation δ (refineLattice e he x) := by
  ext n
  by_cases hn : ∃ m : ℤ, (e : ℤ) * m = n
  · obtain ⟨m, rfl⟩ := hn
    simp
  · simp [refineLattice_coeff_off e he _ n hn]

theorem refineLattice_deltaOperator [CharZero F] (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (η : Derivation k F F) (x : LaurentSeries F) :
    refineLattice e he (deltaOperator p η x) =
      deltaOperator (p * e) η (refineLattice e he x) := by
  ext n
  by_cases hn : ∃ m : ℤ, (e : ℤ) * m = n
  · obtain ⟨m, rfl⟩ := hn
    have hi : (e : ℤ) * m - ((p * e : ℕ) : ℤ) = (e : ℤ) * (m - p) := by
      push_cast
      ring
    rw [refineLattice_coeff, deltaOperator_coeff, deltaOperator_coeff, hi, refineLattice_coeff]
    have hp' : (p : F) ≠ 0 := by exact_mod_cast hp.ne'
    have he' : (e : F) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp
  · have hn' : ¬ ∃ m : ℤ, (e : ℤ) * m = n - ((p * e : ℕ) : ℤ) := by
      rintro ⟨m, hm⟩
      apply hn
      refine ⟨m + p, ?_⟩
      push_cast at hm ⊢
      nlinarith
    rw [refineLattice_coeff_off e he _ n hn, deltaOperator_coeff,
      refineLattice_coeff_off e he _ _ hn']
    simp

theorem refineLattice_starTerm [CharZero F] (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (x y : LaurentSeries F) (j : ℕ) :
    refineLattice e he (starTerm p δ η x y j) =
      starTerm (p * e) δ η (refineLattice e he x) (refineLattice e he y) j := by
  have hΔ : Function.Semiconj (refineLattice e he) (deltaOperator p η)
      (deltaOperator (p * e) η) := refineLattice_deltaOperator p e hp he η
  have hD : Function.Semiconj (refineLattice e he) (coefficientDerivation δ)
      (coefficientDerivation δ) := refineLattice_coefficientDerivation e he δ
  simp [starTerm, hΔ.iterate_right j x, hD.iterate_right j y]

/-- Lattice refinement preserves the actual infinite star multiplication. -/
theorem refineLattice_starProduct [CharZero F] (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (x y : LaurentSeries F) :
    refineLattice e he (starProduct p hp δ η x y) =
      starProduct (p * e) (Nat.mul_pos hp he) δ η
        (refineLattice e he x) (refineLattice e he y) := by
  ext n
  rw [starProduct_coeff]
  simp_rw [← refineLattice_starTerm p e hp he δ η x y]
  by_cases hn : ∃ m : ℤ, (e : ℤ) * m = n
  · obtain ⟨m, rfl⟩ := hn
    simp only [refineLattice_coeff, starProduct_coeff]
  · simp [refineLattice_coeff_off e he _ n hn]

/-- The algebra embedding induced by multiplying the denominator by e. -/
def refineLatticeAlgHom [CharZero F] (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (δ η : Derivation k F F) (h : Function.Commute δ η) :
    StarSeries p hp δ η h →ₐ[k] StarSeries (p * e) (Nat.mul_pos hp he) δ η h where
  toFun x := StarSeries.ofSeries (refineLattice e he (StarSeries.toSeries x))
  map_zero' := refineLattice_zero e he
  map_one' := refineLattice_one e he
  map_add' := refineLattice_add e he
  map_mul' := refineLattice_starProduct p e hp he δ η
  commutes' a := by
    change refineLattice e he (single 0 (algebraMap k F a)) = single 0 (algebraMap k F a)
    simp

theorem lowerBound_refineLattice_iff (e : ℕ) (he : 0 < e) (b : ℤ) (x : LaurentSeries F) :
    LowerBound ((e : ℤ) * b) (refineLattice e he x) ↔ LowerBound b x := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  constructor
  · intro h n hn
    have hz := h ((e : ℤ) * n) (by nlinarith)
    simpa using hz
  · intro h n hn
    by_cases hm : ∃ m : ℤ, (e : ℤ) * m = n
    · obtain ⟨m, rfl⟩ := hm
      rw [refineLattice_coeff]
      exact h m (by nlinarith)
    · exact refineLattice_coeff_off e he x n hm

@[simp] theorem refineLattice_distinguished (p e : ℕ) (he : 0 < e) :
    refineLattice (F := F) e he (distinguishedSymbol p) = distinguishedSymbol (p * e) := by
  simp only [distinguishedSymbol, refineLattice_single]
  congr 1
  push_cast
  ring_nf

end LatticeRefinement

end MakarLimanov.SymbolSeries
