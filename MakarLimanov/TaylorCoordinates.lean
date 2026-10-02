import MakarLimanov.TaylorSeries
import MakarLimanov.SymbolSeries

/-! The double Taylor embedding and the coordinate differential operators of §6. -/

namespace MakarLimanov.TaylorCoordinates

open TaylorSeries HahnSeries Finset

attribute [local instance 2000] HahnSeries.instAlgebra

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The outer variable is `t` and the inner variable is `w`. -/
abbrev BiSeries (F : Type*) := PowerSeries (PowerSeries F)

/-- Differentiation in the outer variable. -/
noncomputable def partialT : BiSeries F →+ BiSeries F :=
  { toFun := PowerSeries.derivativeFun
    map_zero' := by ext i j; simp [PowerSeries.coeff_derivativeFun]
    map_add' := PowerSeries.derivativeFun_add }

/-- Differentiation in the inner variable, applied to every outer coefficient. -/
noncomputable def partialW : BiSeries F →+ BiSeries F where
  toFun x := PowerSeries.mk (fun i ↦ PowerSeries.derivative F (PowerSeries.coeff i x))
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp

@[simp] lemma coeff_partialT (x : BiSeries F) (i : ℕ) :
    PowerSeries.coeff i (partialT x) = PowerSeries.coeff (i + 1) x * (i + 1) :=
  PowerSeries.coeff_derivativeFun x i

@[simp] lemma coeff_partialW (x : BiSeries F) (i : ℕ) :
    PowerSeries.coeff i (partialW x) = PowerSeries.derivative F (PowerSeries.coeff i x) :=
  by simp only [partialW, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk]

lemma partialT_mul (x y : BiSeries F) :
    partialT (x * y) = x * partialT y + y * partialT x := by
  simpa only [smul_eq_mul] using PowerSeries.derivativeFun_mul x y

lemma partialW_mul (x y : BiSeries F) :
    partialW (x * y) = x * partialW y + y * partialW x := by
  apply PowerSeries.ext
  intro i
  simp only [coeff_partialW, PowerSeries.coeff_mul, map_sum, Derivation.leibniz,
    smul_eq_mul, map_add, Finset.sum_add_distrib]
  congr 1
  exact Finset.Nat.sum_antidiagonal_swap (f := fun ab ↦
    PowerSeries.coeff ab.1 y * PowerSeries.derivative F (PowerSeries.coeff ab.2 x))

lemma partials_commute : Function.Commute (partialT (F := F)) partialW := by
  intro x
  apply PowerSeries.ext
  intro i
  simp [Derivation.leibniz, smul_eq_mul, mul_comm]

variable [CharZero F]

/-- The first intertwining identity in equation (6.1). -/
lemma partialT_doubleTaylor (δ η : Derivation k F F) (a : F) :
    partialT (doubleTaylor δ η a) = doubleTaylor δ η (δ a) := by
  apply PowerSeries.ext
  intro i
  change PowerSeries.coeff i (PowerSeries.derivativeFun
    (PowerSeries.map (taylor η).toRingHom (taylor δ a))) =
    PowerSeries.coeff i (PowerSeries.map (taylor η).toRingHom (taylor δ (δ a)))
  rw [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_map, ← derivative_taylor,
    PowerSeries.coeff_map, PowerSeries.coeff_derivative]
  simp only [map_mul, map_add, map_natCast, map_one]

/-- The second intertwining identity in equation (6.1). -/
lemma partialW_doubleTaylor (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (a : F) : partialW (doubleTaylor δ η a) = doubleTaylor δ η (η a) := by
  ext i j
  rw [coeff_partialW, PowerSeries.coeff_derivative, doubleTaylor_coeff,
    doubleTaylor_coeff, Function.iterate_succ_apply]
  rw [← (hc.iterate_left i) a]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hj : (j + 1 : F) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp

/-- Extend the Taylor embedding to Laurent coefficients. -/
noncomputable def taylorLaurent (δ η : Derivation k F F) (x : LaurentSeries F) :
    LaurentSeries (BiSeries F) := x.map (doubleTaylor δ η).toRingHom

@[simp] lemma taylorLaurent_coeff (δ η : Derivation k F F) (x : LaurentSeries F) (n : ℤ) :
    (taylorLaurent δ η x).coeff n = doubleTaylor δ η (x.coeff n) := rfl

lemma taylorLaurent_injective (δ η : Derivation k F F) :
    Function.Injective (taylorLaurent δ η) := by
  intro x y h
  ext n
  exact doubleTaylor_injective δ η (congrArg (fun z ↦ z.coeff n) h)

/-- Elements killed by the derivation have constant Taylor series. -/
lemma taylor_of_constant (D : Derivation k F F) (a : F) (ha : D a = 0) :
    taylor D a = PowerSeries.C a := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_C]
  | succ n =>
    have hz : D^[n] (0 : F) = 0 := by simp
    simp [coeff_series, Function.iterate_succ_apply, ha, hz]

lemma doubleTaylor_of_constant (δ η : Derivation k F F) (a : F)
    (hδ : δ a = 0) (hη : η a = 0) :
    doubleTaylor δ η a = PowerSeries.C (PowerSeries.C a) := by
  change PowerSeries.map (taylor η).toRingHom (taylor δ a) = _
  rw [taylor_of_constant δ a hδ, PowerSeries.map_C]
  exact congrArg PowerSeries.C (taylor_of_constant η a hη)

/-- The `t` derivative on Laurent series acts only on their double-series coefficients. -/
noncomputable def coordinateT (x : LaurentSeries (BiSeries F)) :
    LaurentSeries (BiSeries F) := x.map partialT

/-- The exponent Euler operator in the Laurent coordinate `z^(-1/p)`. -/
noncomputable def coordinateEuler (x : LaurentSeries (BiSeries F)) :
    LaurentSeries (BiSeries F) where
  coeff n := (n : BiSeries F) * x.coeff n
  isPWO_support' := x.isPWO_support.mono <| by
    intro n hn
    simp only [Function.mem_support] at hn ⊢
    exact fun h ↦ hn (by simp [h])

/-- In the coordinate `z^(-1/p)`, this is `∂z + z⁻¹ ∂w`. -/
noncomputable def coordinateDelta (p : ℕ) (x : LaurentSeries (BiSeries F)) :
    LaurentSeries (BiSeries F) :=
  single (p : ℤ) 1 * (x.map partialW -
    single 0 (PowerSeries.C (PowerSeries.C ((p : F)⁻¹))) * coordinateEuler x)

omit [CharZero F] in
@[simp] lemma coordinateT_coeff (x : LaurentSeries (BiSeries F)) (n : ℤ) :
    (coordinateT x).coeff n = partialT (x.coeff n) := rfl

omit [CharZero F] in
@[simp] lemma coordinateDelta_coeff (p : ℕ) (x : LaurentSeries (BiSeries F)) (n : ℤ) :
    (coordinateDelta p x).coeff n = partialW (x.coeff (n - p)) -
      PowerSeries.C (PowerSeries.C ((p : F)⁻¹)) * (n - p : ℤ) * x.coeff (n - p) := by
  simp [coordinateDelta, coordinateEuler, coeff_single_mul, mul_assoc]

/-- Taylor coefficients intertwine the symbol's first derivation with `∂t`. -/
lemma coordinateT_taylorLaurent (δ η : Derivation k F F) (x : LaurentSeries F) :
    coordinateT (taylorLaurent δ η x) =
      taylorLaurent δ η (SymbolSeries.coefficientDerivation δ x) := by
  apply HahnSeries.ext
  funext n
  exact partialT_doubleTaylor δ η (x.coeff n)

/-- Equation (6.2): Taylor coefficients intertwine `Δ` with `∂z + z⁻¹ ∂w`. -/
lemma coordinateDelta_taylorLaurent (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (x : LaurentSeries F) :
    coordinateDelta p (taylorLaurent δ η x) =
      taylorLaurent δ η (SymbolSeries.deltaOperator p η x) := by
  ext n
  simp only [coordinateDelta_coeff, taylorLaurent_coeff, SymbolSeries.deltaOperator_coeff,
    map_sub, map_mul, map_intCast, partialW_doubleTaylor δ η hc]
  rw [doubleTaylor_of_constant δ η ((p : F)⁻¹)]
  · simp [Derivation.leibniz_inv]
  · simp [Derivation.leibniz_inv]

lemma coordinateT_iterate_taylorLaurent (δ η : Derivation k F F)
    (x : LaurentSeries F) (n : ℕ) :
    coordinateT^[n] (taylorLaurent δ η x) =
      taylorLaurent δ η ((SymbolSeries.coefficientDerivation δ)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', ih] using
      coordinateT_taylorLaurent δ η ((SymbolSeries.coefficientDerivation δ)^[n] x)

lemma coordinateDelta_iterate_taylorLaurent (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (x : LaurentSeries F) (n : ℕ) :
    (coordinateDelta p)^[n] (taylorLaurent δ η x) =
      taylorLaurent δ η ((SymbolSeries.deltaOperator p η)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', ih] using
      coordinateDelta_taylorLaurent δ η hc p ((SymbolSeries.deltaOperator p η)^[n] x)

@[simp] lemma taylorLaurent_mul (δ η : Derivation k F F) (x y : LaurentSeries F) :
    taylorLaurent δ η (x * y) = taylorLaurent δ η x * taylorLaurent δ η y :=
  HahnSeries.map_mul (doubleTaylor δ η).toRingHom.toNonUnitalRingHom

@[simp] lemma taylorLaurent_single (δ η : Derivation k F F) (n : ℤ) (a : F) :
    taylorLaurent δ η (single n a) = single n (doubleTaylor δ η a) := by
  apply HahnSeries.ext
  funext m
  by_cases hm : m = n <;> simp [hm]

/-- A lower exponent bound, also valid when the coefficient ring is not a field. -/
def CoordinateBound (b : ℤ) (x : LaurentSeries (BiSeries F)) : Prop :=
  ∀ n : ℤ, n < b → x.coeff n = 0

omit [CharZero F] in
lemma coordinateBound_order (x : LaurentSeries (BiSeries F)) :
    CoordinateBound x.order x := fun _ h ↦ coeff_eq_zero_of_lt_order h

omit [CharZero F] in
lemma CoordinateBound.mul {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) :
    CoordinateBound (b + c) (x * y) := by
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hi : b ≤ ij.1 := by
    by_contra! hi
    exact (mem_addAntidiagonal.mp hij).1 (hx _ hi)
  have hj : c ≤ ij.2 := by
    by_contra! hj
    exact (mem_addAntidiagonal.mp hij).2.1 (hy _ hj)
  have hs := (mem_addAntidiagonal.mp hij).2.2
  omega

omit [CharZero F] in
lemma CoordinateBound.coordinateT {b : ℤ} {x : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) : CoordinateBound b (coordinateT x) := by
  intro n hn
  simp [hx n hn]

omit [CharZero F] in
lemma CoordinateBound.coordinateDelta {b : ℤ} {x : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (p : ℕ) :
    CoordinateBound (b + p) (coordinateDelta p x) := by
  intro n hn
  simp [hx (n - p) (by omega)]

omit [CharZero F] in
lemma CoordinateBound.coordinateT_iterate {b : ℤ} {x : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (j : ℕ) :
    CoordinateBound b (TaylorCoordinates.coordinateT^[j] x) := by
  induction j with
  | zero => exact hx
  | succ j ih => simpa only [Function.iterate_succ_apply'] using ih.coordinateT

omit [CharZero F] in
lemma CoordinateBound.coordinateDelta_iterate {b : ℤ} {x : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (p j : ℕ) :
    CoordinateBound (b + (p : ℤ) * j) ((TaylorCoordinates.coordinateDelta p)^[j] x) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    convert ih.coordinateDelta p using 1 <;>
      simp [Function.iterate_succ_apply', mul_add, add_assoc]

/-- The summands of the coordinate product (6.3), defined for arbitrary coordinate series. -/
noncomputable def diamondTerm (p : ℕ) (x y : LaurentSeries (BiSeries F)) (j : ℕ) :
    LaurentSeries (BiSeries F) :=
  single 0 (PowerSeries.C (PowerSeries.C ((j.factorial : F)⁻¹))) *
    ((coordinateDelta p)^[j] x * coordinateT^[j] y)

omit [CharZero F] in
lemma diamondTerm_bound (p : ℕ) {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) (j : ℕ) :
    CoordinateBound (b + c + (p : ℤ) * j) (diamondTerm p x y j) := by
  have h := (hx.coordinateDelta_iterate p j).mul (hy.coordinateT_iterate j)
  intro n hn
  simp [diamondTerm, h n (by omega)]

/-- The coordinate product is coefficientwise finite because each `Δ` raises the lower bound. -/
noncomputable def diamondFamily (p : ℕ) (hp : 0 < p)
    (x y : LaurentSeries (BiSeries F)) : SummableFamily ℤ (BiSeries F) ℕ where
  toFun := diamondTerm p x y
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨x.order + y.order, ?_⟩
    intro n hn
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hn
    change (diamondTerm p x y j).coeff n ≠ 0 at hj
    by_contra! h
    apply hj
    apply diamondTerm_bound p (coordinateBound_order x) (coordinateBound_order y)
    have hnonneg : (0 : ℤ) ≤ (p : ℤ) * j := mul_nonneg (by omega) (by omega)
    omega
  finite_co_support' n := by
    apply (Set.finite_Iic (n - (x.order + y.order)).toNat).subset
    intro j hj
    change j ≤ (n - (x.order + y.order)).toNat
    have h : x.order + y.order + (p : ℤ) * j ≤ n := by
      by_contra! h
      exact hj (diamondTerm_bound p (coordinateBound_order x) (coordinateBound_order y) j n h)
    have hp' : (1 : ℤ) ≤ p := by omega
    have hj' : (0 : ℤ) ≤ j := by omega
    have : (j : ℤ) ≤ n - (x.order + y.order) := by nlinarith
    omega

/-- The actual infinite coordinate product of equation (6.3). -/
noncomputable def diamond (p : ℕ) (hp : 0 < p) (x y : LaurentSeries (BiSeries F)) :
    LaurentSeries (BiSeries F) := (diamondFamily p hp x y).hsum

lemma diamondTerm_taylorLaurent (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (x y : LaurentSeries F) (j : ℕ) :
    diamondTerm p (taylorLaurent δ η x) (taylorLaurent δ η y) j =
      taylorLaurent δ η (SymbolSeries.starTerm p δ η x y j) := by
  rw [diamondTerm, SymbolSeries.starTerm, ← single_zero_mul_eq_smul,
    taylorLaurent_mul, taylorLaurent_single, taylorLaurent_mul,
    coordinateDelta_iterate_taylorLaurent δ η hc, coordinateT_iterate_taylorLaurent]
  rw [doubleTaylor_of_constant δ η ((j.factorial : F)⁻¹)] <;>
    simp [Derivation.leibniz_inv]

/-- The Taylor embedding preserves the infinite star product, not only its individual terms. -/
lemma diamond_taylorLaurent (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (x y : LaurentSeries F) :
    diamond p hp (taylorLaurent δ η x) (taylorLaurent δ η y) =
      taylorLaurent δ η (SymbolSeries.starProduct p hp δ η x y) := by
  apply HahnSeries.ext
  funext n
  change (∑ᶠ j, (diamondTerm p (taylorLaurent δ η x) (taylorLaurent δ η y) j).coeff n) =
    (doubleTaylor δ η).toLinearMap (∑ᶠ j, (SymbolSeries.starTerm p δ η x y j).coeff n)
  rw [map_finsum (doubleTaylor δ η).toLinearMap
    (f := fun j ↦ (SymbolSeries.starTerm p δ η x y j).coeff n)
    ((SymbolSeries.starFamily p hp δ η x y).finite_co_support n)]
  apply finsum_congr
  intro j
  exact congrArg (fun z ↦ z.coeff n) (diamondTerm_taylorLaurent δ η hc p x y j)

end MakarLimanov.TaylorCoordinates
