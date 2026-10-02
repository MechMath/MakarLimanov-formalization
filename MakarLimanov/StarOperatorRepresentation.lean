import MakarLimanov.NormalOrderedOperatorProduct
import MakarLimanov.FallingBasisSymbol
import MakarLimanov.StarMonomialIndependence
import MakarLimanov.StarConstantLinearity

/-!
# Finite representations of concrete star symbols by differential operators

Finite combinations of the concrete Laurent monomials act as ordinary
normal-ordered differential operators.  Their finite multiplication tables
agree, so this representation transports nonvanishing from operators to
symbols.
-/

noncomputable section

namespace MakarLimanov.StarOperatorRepresentation

open Polynomial NormalOrderedOperatorProduct
open HahnSeries SymbolSeries TwoVariableDifferentialField ConcreteStarMonomials
open StarMonomialIndependence StarConstantLinearity

attribute [local instance 2000] HahnSeries.instAlgebra

universe u

variable {C : Type u} [Field C]

/-- The finite coefficient data for concrete monomials. -/
abbrev Coefficients (C : Type*) [Field C] := (ℕ × ℕ × ℕ) →₀ C

/-- The ordinary differential operator represented by finite monomial data. -/
def operatorLinearMap : Coefficients C →ₗ[C] Module.End C (Polynomial C) :=
  Finsupp.linearCombination C (fun t ↦ operatorMonomial t.1 t.2.2)

@[simp] theorem operatorLinearMap_apply (v : Coefficients C) :
    operatorLinearMap v = v.sum (fun t c ↦ c • operatorMonomial t.1 t.2.2) := rfl

@[simp] theorem operatorLinearMap_single (t : ℕ × ℕ × ℕ) (c : C) :
    operatorLinearMap (Finsupp.single t c) = c • operatorMonomial t.1 t.2.2 := by
  simp [operatorLinearMap]

/-- The common finite product table for a pair of basis monomials. -/
def monomialProduct (a b : ℕ × ℕ × ℕ) : Coefficients C :=
  ∑ i ∈ Finset.range (min a.2.2 b.1 + 1),
    Finsupp.single (a.1 + b.1 - i, a.2.1 + b.2.1, a.2.2 + b.2.2 - i)
      ((a.2.2.choose i * b.1.descFactorial i : ℕ) : C)

theorem operatorLinearMap_monomialProduct (a b : ℕ × ℕ × ℕ) :
    operatorLinearMap (monomialProduct (C := C) a b) =
      operatorMonomial a.1 a.2.2 * operatorMonomial b.1 b.2.2 := by
  simp only [monomialProduct, map_sum, operatorLinearMap_single,
    operatorMonomial_mul]

/-- Extend the common product table to arbitrary finite coefficient data. -/
def coefficientProduct (v w : Coefficients C) : Coefficients C :=
  v.sum (fun a c ↦ w.sum (fun b e ↦ (c * e) • monomialProduct a b))

theorem operatorLinearMap_coefficientProduct (v w : Coefficients C) :
    operatorLinearMap (coefficientProduct v w) =
      operatorLinearMap v * operatorLinearMap w := by
  classical
  simp only [coefficientProduct, Finsupp.sum, map_sum, map_smul,
    operatorLinearMap_monomialProduct]
  simp only [operatorLinearMap_apply, Finsupp.sum, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm]

/-- A concrete symbol and an operator represented by the same finite data. -/
def Rep (U : LaurentSeries (RationalField C)) (T : Module.End C (Polynomial C)) : Prop :=
  ∃ v : Coefficients C, symbolLinearMap (C := C) v = U ∧ operatorLinearMap v = T

theorem Rep.zero : Rep (0 : LaurentSeries (RationalField C)) 0 :=
  ⟨0, map_zero _, map_zero _⟩

theorem Rep.add {U V : LaurentSeries (RationalField C)}
    {S T : Module.End C (Polynomial C)} (hU : Rep U S) (hV : Rep V T) :
    Rep (U + V) (S + T) := by
  obtain ⟨v, rfl, rfl⟩ := hU
  obtain ⟨w, rfl, rfl⟩ := hV
  exact ⟨v + w, map_add _ _ _, map_add _ _ _⟩

theorem Rep.smul {U : LaurentSeries (RationalField C)}
    {T : Module.End C (Polynomial C)} (hU : Rep U T) (c : C) :
    Rep (c • U) (c • T) := by
  obtain ⟨v, rfl, rfl⟩ := hU
  exact ⟨c • v, map_smul _ _ _, map_smul _ _ _⟩

theorem Rep.monomial (l Q d : ℕ) :
    Rep (ConcreteStarMonomials.monomial (C := C) l Q d) (operatorMonomial l d) := by
  refine ⟨Finsupp.single (l, Q, d) 1, ?_, ?_⟩
  · rw [symbolLinearMap_single]
    exact one_smul C _
  · rw [operatorLinearMap_single]
    exact one_smul C _

theorem Rep.sum {ι : Type*} (s : Finset ι)
    (U : ι → LaurentSeries (RationalField C)) (T : ι → Module.End C (Polynomial C))
    (h : ∀ i ∈ s, Rep (U i) (T i)) :
    Rep (∑ i ∈ s, U i) (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep.zero (C := C)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

theorem Rep.one : Rep (1 : LaurentSeries (RationalField C)) 1 := by
  have hs : ConcreteStarMonomials.monomial (C := C) 0 0 0 = 1 := by
    simp [ConcreteStarMonomials.monomial, coefficient]
  have ho : operatorMonomial (C := C) 0 0 = 1 := by
    ext P
    simp
  simpa only [hs, ho] using Rep.monomial (C := C) 0 0 0

theorem Rep.derivative : Rep (distinguishedSymbol 1 : LaurentSeries (RationalField C))
    (Polynomial.derivative : Module.End C (Polynomial C)) := by
  have hs : ConcreteStarMonomials.monomial (C := C) 0 0 1 = distinguishedSymbol 1 := by
    simp [ConcreteStarMonomials.monomial, coefficient, distinguishedSymbol]
  have ho : operatorMonomial (C := C) 0 1 = Polynomial.derivative := by
    ext P
    simp
  simpa only [hs, ho] using Rep.monomial (C := C) 0 0 1

/-- The zero symbol can represent only the zero operator. -/
theorem Rep.operator_eq_zero {T : Module.End C (Polynomial C)}
    (hT : Rep (0 : LaurentSeries (RationalField C)) T) : T = 0 := by
  obtain ⟨v, hv, rfl⟩ := hT
  have hv0 : v = 0 := symbolLinearMap_injective (by simpa using hv)
  rw [hv0, map_zero]

/-- A nonzero represented operator certifies nonvanishing of its symbol. -/
theorem Rep.symbol_ne_zero {U : LaurentSeries (RationalField C)}
    {T : Module.End C (Polynomial C)} (hU : Rep U T) (hT : T ≠ 0) : U ≠ 0 := by
  intro h
  subst U
  exact hT hU.operator_eq_zero

variable {k : Type*} [Field k] [Algebra k C] [CharZero C]

/-- The falling-basis coefficient polynomial represents its Euler operator. -/
theorem Rep.fallingPolynomial (P : Polynomial C) :
    Rep (HahnSeries.single 0
      (MvPolynomial.aeval ![tau, upsilon] (FallingBasisSymbol.coefficientPolynomial P)))
      (Polynomial.aeval (DifferentialSeparation.euler (K := C)) P) := by
  let c := FallingBasisSymbol.coefficients P
  have hrep := Rep.sum c.support
    (fun j ↦ c j • ConcreteStarMonomials.monomial (C := C) j j j)
    (fun j ↦ c j • operatorMonomial (C := C) j j)
    (fun j _ ↦ (Rep.monomial (C := C) j j j).smul (c j))
  have hs : (∑ j ∈ c.support, c j • ConcreteStarMonomials.monomial (C := C) j j j) =
      HahnSeries.single 0
        (MvPolynomial.aeval ![tau, upsilon] (FallingBasisSymbol.coefficientPolynomial P)) := by
    rw [FallingBasisSymbol.aeval_coefficientPolynomial]
    ext n
    simp [c, Finsupp.sum, ConcreteStarMonomials.monomial, coefficient,
      Algebra.smul_def, HahnSeries.coeff_single, Finset.sum_ite_irrel, mul_assoc]
  have ho : (∑ j ∈ c.support, c j • operatorMonomial (C := C) j j) =
      Polynomial.aeval (DifferentialSeparation.euler (K := C)) P := by
    simpa only [Finsupp.sum, FallingBasisSymbol.fallingOperator_eq_mulLeft_derivative_pow,
      operatorMonomial] using FallingBasisSymbol.sum_fallingOperator P
  rw [hs, ho] at hrep
  exact hrep

/-- The separating coefficient represents the interpolated diagonal operator. -/
theorem Rep.diagonal (A : ℕ) (values : Fin (A + 1) → C) :
    Rep (HahnSeries.single 0
      (MvPolynomial.aeval ![tau, upsilon] (FallingBasisSymbol.diagonalCoefficient A values)))
      (DifferentialSeparation.diagonalOperator A values) :=
  Rep.fallingPolynomial (DifferentialSeparation.interpolatingPolynomial A values)

theorem symbolLinearMap_monomialProduct (a b : ℕ × ℕ × ℕ) :
    symbolLinearMap (C := C) (monomialProduct (C := C) a b) =
      starProduct 1 (by decide) (delta (k := k) (C := C)) (eta (k := k) (C := C))
        (ConcreteStarMonomials.monomial a.1 a.2.1 a.2.2)
        (ConcreteStarMonomials.monomial b.1 b.2.1 b.2.2) := by
  simp only [monomialProduct, map_sum, symbolLinearMap_single,
    monomial_starProduct, Nat.cast_mul]

theorem symbolLinearMap_coefficientProduct (v w : Coefficients C) :
    symbolLinearMap (C := C) (coefficientProduct v w) =
      starProduct 1 (by decide) (delta (k := k) (C := C)) (eta (k := k) (C := C))
        (symbolLinearMap (C := C) v) (symbolLinearMap (C := C) w) := by
  simp only [coefficientProduct, Finsupp.sum, map_sum, map_smul,
    symbolLinearMap_monomialProduct (k := k)]
  simp only [symbolLinearMap_apply, Finsupp.sum, starProduct_sum_left,
    starProduct_sum_right,
    starProduct_C_smul_left (C := C) 1 (by decide) (delta (k := k) (C := C))
      (eta (k := k) (C := C)) (eta_base (k := k) (C := C)),
    starProduct_C_smul_right (C := C) 1 (by decide) (delta (k := k) (C := C))
      (eta (k := k) (C := C)) (delta_base (k := k) (C := C)),
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm]

/-- Multiplication respects the common finite monomial representation. -/
theorem Rep.mul {U V : LaurentSeries (RationalField C)}
    {S T : Module.End C (Polynomial C)} (hU : Rep U S) (hV : Rep V T) :
    Rep (starProduct 1 (by decide) (delta (k := k) (C := C))
      (eta (k := k) (C := C)) U V) (S * T) := by
  obtain ⟨v, rfl, rfl⟩ := hU
  obtain ⟨w, rfl, rfl⟩ := hV
  exact ⟨coefficientProduct v w, symbolLinearMap_coefficientProduct (k := k) v w,
    operatorLinearMap_coefficientProduct v w⟩

/-- Evaluation of a free polynomial preserves the finite representation. -/
theorem evaluateAt_rep {U : LaurentSeries (RationalField C)}
    {T : Module.End C (Polynomial C)} (hU : Rep U T) (f : FreeAlgebra k Bool) :
    Rep (StarSeries.toSeries (StarSeries.evaluateAt (p := 1) (hp := by decide)
      (h := TwoVariableDifferentialField.commute (k := k) (C := C)) U f))
      (FreeAlgebra.lift k (fun b ↦ if b then T else Polynomial.derivative) f) := by
  induction f with
  | grade0 a =>
    simp only [AlgHom.commutes, StarSeries.toSeries_algebraMap]
    have hh := (Rep.one (C := C)).smul (algebraMap k C a)
    convert hh using 1
    · ext n
      simp [Algebra.smul_def, HahnSeries.coeff_single,
        ← IsScalarTower.algebraMap_apply k C (RationalField C)]
    · ext P
      simp [Module.algebraMap_end_apply, algebraMap_smul]
  | grade1 b =>
    cases b
    · simpa only [StarSeries.evaluateAt_false, FreeAlgebra.lift_ι_apply,
        Bool.false_eq_true, if_false] using Rep.derivative (C := C)
    · simpa only [StarSeries.evaluateAt_true, FreeAlgebra.lift_ι_apply, if_true] using hU
  | add f g hf hg =>
    simp only [map_add, StarSeries.toSeries_add]
    exact hf.add hg
  | mul f g hf hg =>
    simp only [map_mul, StarSeries.toSeries_mul]
    exact hf.mul hg

/-- Any represented nonzero operator value gives a nonzero star-symbol value. -/
theorem evaluateAt_ne_zero_of_operator_ne_zero {U : LaurentSeries (RationalField C)}
    {T : Module.End C (Polynomial C)} (hU : Rep U T) (f : FreeAlgebra k Bool)
    (hf : FreeAlgebra.lift k (fun b ↦ if b then T else Polynomial.derivative) f ≠ 0) :
    StarSeries.toSeries (StarSeries.evaluateAt (p := 1) (hp := by decide)
      (h := TwoVariableDifferentialField.commute (k := k) (C := C)) U f) ≠ 0 :=
  (evaluateAt_rep hU f).symbol_ne_zero hf

/-- The diagonal differential model supplies a concrete nonzero symbol value. -/
theorem diagonal_evaluateAt_ne_zero_of_operator_ne_zero
    (A : ℕ) (values : Fin (A + 1) → C) (f : FreeAlgebra k Bool)
    (hf : FreeAlgebra.lift k (DifferentialSeparation.operatorInput A values) f ≠ 0) :
    StarSeries.toSeries (StarSeries.evaluateAt (p := 1) (hp := by decide)
      (h := TwoVariableDifferentialField.commute (k := k) (C := C))
      (HahnSeries.single 0
        (MvPolynomial.aeval ![tau, upsilon] (FallingBasisSymbol.diagonalCoefficient A values)))
      f) ≠ 0 :=
  evaluateAt_ne_zero_of_operator_ne_zero (Rep.diagonal A values) f hf

end MakarLimanov.StarOperatorRepresentation

end
