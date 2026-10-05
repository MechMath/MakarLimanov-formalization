import MakarLimanov.WordSeparation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The polynomial differential model for word separation

The derivative acts as the shift on divided powers.  Lagrange interpolation in the Euler
operator constructs a differential operator with independently prescribed diagonal entries.
-/

namespace MakarLimanov.DifferentialSeparation

noncomputable section

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The divided-power basis used in the separation argument. -/
def dividedPower (n : ℕ) : Polynomial K := monomial n ((n.factorial : K)⁻¹)

omit [CharZero K] in
@[simp] theorem coeff_dividedPower (n m : ℕ) :
    (dividedPower (K := K) n).coeff m = if n = m then (n.factorial : K)⁻¹ else 0 := by
  simp [dividedPower, coeff_monomial]

omit [CharZero K] in
@[simp] theorem dividedPower_zero : dividedPower (K := K) 0 = 1 := by
  simp [dividedPower]

theorem dividedPower_ne_zero (n : ℕ) : dividedPower (K := K) n ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial K ↦ p.coeff n) h
  simp only [coeff_dividedPower, ↓reduceIte, coeff_zero] at hc
  exact (inv_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero)) hc

/-- Differentiation is exactly an unweighted shift on divided powers. -/
theorem derivative_dividedPower_succ (n : ℕ) :
    derivative (dividedPower (K := K) (n + 1)) = dividedPower n := by
  rw [dividedPower, derivative_monomial_succ, dividedPower]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hf : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  push_cast at hn ⊢
  field_simp

/-- The Euler differential operator `τ d/dτ`. -/
def euler : Module.End K (Polynomial K) := (LinearMap.mulLeft K X).comp derivative

/-- The divided powers are eigenvectors of the Euler operator. -/
theorem euler_dividedPower (n : ℕ) :
    euler (dividedPower (K := K) n) = (n : K) • dividedPower n := by
  simp only [euler, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    dividedPower, derivative_monomial, smul_monomial, smul_eq_mul]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, X_mul_monomial]
    congr 1
    ring

/-- Interpolate arbitrary independent diagonal entries at reversed integer nodes. -/
def interpolatingPolynomial (A : ℕ) (values : Fin (A + 1) → K) : Polynomial K :=
  Lagrange.interpolate Finset.univ (fun i : Fin (A + 1) ↦ ((A - i.val : ℕ) : K)) values

theorem interpolation_nodes_injective (A : ℕ) :
    Function.Injective (fun i : Fin (A + 1) ↦ ((A - i.val : ℕ) : K)) := by
  intro i j h
  have hn : A - i.val = A - j.val := Nat.cast_injective h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

@[simp] theorem eval_interpolatingPolynomial (A : ℕ) (values : Fin (A + 1) → K)
    (i : Fin (A + 1)) :
    (interpolatingPolynomial A values).eval ((A - i.val : ℕ) : K) = values i := by
  exact Lagrange.eval_interpolate_at_node values
    (interpolation_nodes_injective A).injOn (Finset.mem_univ i)

/-- The polynomial differential operator `P(τ d/dτ)` from the paper. -/
def diagonalOperator (A : ℕ) (values : Fin (A + 1) → K) : Module.End K (Polynomial K) :=
  aeval euler (interpolatingPolynomial A values)

/-- The interpolated operator realizes every chosen diagonal entry. -/
theorem diagonalOperator_dividedPower (A : ℕ) (values : Fin (A + 1) → K)
    (i : Fin (A + 1)) :
    diagonalOperator A values (dividedPower (A - i.val)) = values i • dividedPower (A - i.val) := by
  unfold diagonalOperator
  rw [Module.End.aeval_apply_of_hasEigenvector
    ⟨(Module.End.mem_eigenspace_iff.mpr (euler_dividedPower (A - i.val))),
      dividedPower_ne_zero (A - i.val)⟩]
  rw [eval_interpolatingPolynomial]

open Matrix

/-- The finite shift matrix over the differential coefficient field. -/
def shift (A : ℕ) : Matrix (Fin (A + 1)) (Fin (A + 1)) K :=
  fun i j ↦ if i.val = j.val + 1 then 1 else 0

/-- Embed the finite basis, in reversed order, as divided powers. -/
def basisEmbedding (A : ℕ) : (Fin (A + 1) → K) →ₗ[K] Polynomial K where
  toFun v := ∑ i : Fin (A + 1), v i • dividedPower (A - i.val)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

omit [CharZero K] in
@[simp] theorem basisEmbedding_single (A : ℕ) (i : Fin (A + 1)) (c : K) :
    basisEmbedding A (Pi.single i c) = c • dividedPower (A - i.val) := by
  simp [basisEmbedding, Pi.single_apply]

/-- The coefficient of each divided power recovers its unique input coordinate. -/
theorem coeff_basisEmbedding (A : ℕ) (v : Fin (A + 1) → K) (i : Fin (A + 1)) :
    (basisEmbedding A v).coeff (A - i.val) = v i * ((A - i.val).factorial : K)⁻¹ := by
  simp only [basisEmbedding, LinearMap.coe_mk, AddHom.coe_mk, finset_sum_coeff,
    coeff_smul, coeff_dividedPower]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hn : A - j.val ≠ A - i.val := by
      intro hh
      apply hji
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp [hn]
  · simp

/-- The finite polynomial subspace embeds faithfully into the differential model. -/
theorem basisEmbedding_injective (A : ℕ) : Function.Injective (basisEmbedding (K := K) A) := by
  intro v w h
  funext i
  have hc := congrArg (fun p : Polynomial K ↦ p.coeff (A - i.val)) h
  rw [coeff_basisEmbedding, coeff_basisEmbedding] at hc
  exact mul_right_cancel₀ (inv_ne_zero (Nat.cast_ne_zero.mpr (A - i.val).factorial_ne_zero)) hc

omit [CharZero K] in
theorem shift_single (A : ℕ) (i : Fin (A + 1)) (c : K) :
    shift A *ᵥ Pi.single i c =
      if hi : i.val < A then Pi.single ⟨i.val + 1, by omega⟩ c else 0 := by
  rw [Matrix.mulVec_single]
  ext j
  by_cases hi : i.val < A
  · simp [shift, Matrix.col_apply, hi, Pi.single_apply, Fin.ext_iff]
  · have hj : j.val ≠ i.val + 1 := by have hj := j.isLt; omega
    simp [shift, Matrix.col_apply, hi, hj]

/-- Ordinary differentiation restricts to the finite shift matrix. -/
theorem derivative_basisEmbedding (A : ℕ) (v : Fin (A + 1) → K) :
    derivative (basisEmbedding A v) = basisEmbedding A (shift A *ᵥ v) := by
  have hh : derivative.comp (basisEmbedding (K := K) A) =
      (basisEmbedding A).comp (shift A).mulVecLin := by
    apply LinearMap.pi_ext
    intro i c
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, basisEmbedding_single, map_smul,
      shift_single]
    split_ifs with hi
    · rw [basisEmbedding_single]
      have hn : A - i.val = (A - (i.val + 1)) + 1 := by omega
      rw [hn, derivative_dividedPower_succ]
    · have hn : A - i.val = 0 := by omega
      simp [hn]
  exact DFunLike.congr_fun hh v

/-- The interpolated Euler polynomial restricts to the prescribed diagonal matrix. -/
theorem diagonalOperator_basisEmbedding (A : ℕ) (values : Fin (A + 1) → K)
    (v : Fin (A + 1) → K) :
    diagonalOperator A values (basisEmbedding A v) =
      basisEmbedding A (Matrix.diagonal values *ᵥ v) := by
  have hh : (diagonalOperator A values).comp (basisEmbedding A) =
      (basisEmbedding A).comp (Matrix.diagonal values).mulVecLin := by
    apply LinearMap.pi_ext
    intro i c
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, basisEmbedding_single, map_smul,
      Matrix.diagonal_mulVec_single, diagonalOperator_dividedPower, smul_smul]
    rw [mul_comm]
  exact DFunLike.congr_fun hh v

variable {k : Type*} [CommRing k] [Algebra k K]

/-- The two differential operators representing the free generators. -/
def operatorInput (A : ℕ) (values : Fin (A + 1) → K) (b : Bool) :
    Module.End K (Polynomial K) := if b then diagonalOperator A values else derivative

/-- Their restrictions to the finite invariant subspace. -/
def matrixInput (A : ℕ) (values : Fin (A + 1) → K) (b : Bool) :
    Matrix (Fin (A + 1)) (Fin (A + 1)) K :=
  if b then Matrix.diagonal values else shift A

/-- Evaluation of every free polynomial respects the finite invariant subspace. -/
theorem evaluation_basisEmbedding (A : ℕ) (values : Fin (A + 1) → K)
    (f : FreeAlgebra k Bool) (v : Fin (A + 1) → K) :
    FreeAlgebra.lift k (operatorInput A values) f (basisEmbedding A v) =
      basisEmbedding A ((FreeAlgebra.lift k (matrixInput A values) f) *ᵥ v) := by
  induction f generalizing v with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    have hm : (algebraMap k (Matrix (Fin (A + 1)) (Fin (A + 1)) K) c) *ᵥ v = c • v := by
      ext i
      rw [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
      simp [Algebra.smul_def]
    rw [hm]
    change c • basisEmbedding A v = basisEmbedding A (c • v)
    exact ((basisEmbedding A).restrictScalars k).map_smul c v |>.symm
  | grade1 b =>
    simp only [FreeAlgebra.lift_ι_apply]
    cases b
    · exact derivative_basisEmbedding A v
    · exact diagonalOperator_basisEmbedding A values v
  | add f g hf hg =>
    simp only [map_add, LinearMap.add_apply, Matrix.add_mulVec, hf, hg]
  | mul f g hf hg =>
    simp only [map_mul, Module.End.mul_apply, hg, hf, ← Matrix.mulVec_mulVec]

/-- A faithful finite restriction witnesses a nonzero polynomial differential operator. -/
theorem operator_evaluation_ne_zero_of_matrix (A : ℕ) (values : Fin (A + 1) → K)
    (f : FreeAlgebra k Bool)
    (hf : FreeAlgebra.lift k (matrixInput A values) f ≠ 0) :
    FreeAlgebra.lift k (operatorInput A values) f ≠ 0 := by
  intro hz
  apply hf
  apply Matrix.ext_of_mulVec_single
  intro i
  apply basisEmbedding_injective A
  have hh := evaluation_basisEmbedding A values f (Pi.single i 1)
  rw [hz] at hh
  simpa only [LinearMap.zero_apply, Matrix.zero_mulVec, map_zero] using hh.symm

section GenericDiagonal

variable {k : Type*} [Field k] [CharZero k]

/-- The concrete coefficient field of the finite differential model. -/
abbrev CoefficientField (A : ℕ) := FractionRing (MvPolynomial (Fin (A + 1)) k)

/-- The independent diagonal values, embedded into their fraction field. -/
def genericValues (A : ℕ) (i : Fin (A + 1)) : CoefficientField (k := k) A :=
  algebraMap (MvPolynomial (Fin (A + 1)) k) (CoefficientField (k := k) A) (MvPolynomial.X i)

theorem map_matrixInput (A : ℕ) (b : Bool) :
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin (A + 1)) k)
      (CoefficientField (k := k) A)).mapMatrix
      (if b then WordSeparation.diagonalMatrix A else WordSeparation.shiftMatrix A) =
        matrixInput A (genericValues (k := k) A) b := by
  ext i j
  cases b
  · by_cases hij : i.val = j.val + 1 <;>
      simp [WordSeparation.shiftMatrix, matrixInput, shift, hij]
  · by_cases hij : i = j
    · subst j; simp [WordSeparation.diagonalMatrix, matrixInput, genericValues, Matrix.diagonal_apply]
    · simp [WordSeparation.diagonalMatrix, matrixInput, genericValues, Matrix.diagonal_apply, hij]

/-- The nonzero finite matrix witness stays nonzero in its explicit coefficient field. -/
theorem generic_matrix_evaluation_ne_zero (A : ℕ) (f : FreeAlgebra k Bool) (hf : f ≠ 0)
    (hA : ∀ w ∈ (ControlledMatrix.wordCoefficients f).coeff.support,
      WordSeparation.shifts w.toList ≤ A) :
    FreeAlgebra.lift k (matrixInput A (genericValues (k := k) A)) f ≠ 0 := by
  let φ : Matrix (Fin (A + 1)) (Fin (A + 1)) (MvPolynomial (Fin (A + 1)) k) →ₐ[k]
      Matrix (Fin (A + 1)) (Fin (A + 1)) (CoefficientField (k := k) A) :=
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin (A + 1)) k)
      (CoefficientField (k := k) A)).mapMatrix
  have hcomp : φ.comp (FreeAlgebra.lift k (fun b : Bool ↦
      if b then WordSeparation.diagonalMatrix (k := k) A else WordSeparation.shiftMatrix A)) =
      FreeAlgebra.lift k (matrixInput A (genericValues (k := k) A)) := by
    apply FreeAlgebra.hom_ext
    funext b
    simpa only [Function.comp_apply, AlgHom.comp_apply, FreeAlgebra.lift_ι_apply] using
      map_matrixInput (k := k) A b
  have hpoly := WordSeparation.evaluation_ne_zero A f hf hA
  intro hz
  apply hpoly
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun M ↦ M i j) (DFunLike.congr_fun hcomp f)
  rw [hz] at hh
  apply IsFractionRing.injective (MvPolynomial (Fin (A + 1)) k)
    (CoefficientField (k := k) A)
  simpa [φ, Matrix.map_apply] using hh

/-- A genuine polynomial differential operator separates every nonzero bounded polynomial. -/
theorem generic_operator_evaluation_ne_zero (A : ℕ) (f : FreeAlgebra k Bool) (hf : f ≠ 0)
    (hA : ∀ w ∈ (ControlledMatrix.wordCoefficients f).coeff.support,
      WordSeparation.shifts w.toList ≤ A) :
    FreeAlgebra.lift k (operatorInput A (genericValues (k := k) A)) f ≠ 0 := by
  exact operator_evaluation_ne_zero_of_matrix A _ f (generic_matrix_evaluation_ne_zero A f hf hA)

/-- Every nonzero free polynomial is detected by an explicit pair of differential operators. -/
theorem exists_generic_operator_evaluation_ne_zero (f : FreeAlgebra k Bool) (hf : f ≠ 0) :
    ∃ A : ℕ, FreeAlgebra.lift k (operatorInput A (genericValues (k := k) A)) f ≠ 0 := by
  classical
  refine ⟨(ControlledMatrix.wordCoefficients f).coeff.support.sup
    (fun w ↦ WordSeparation.shifts w.toList), ?_⟩
  apply generic_operator_evaluation_ne_zero _ f hf
  intro w hw
  exact Finset.le_sup hw

end GenericDiagonal

end

end MakarLimanov.DifferentialSeparation
