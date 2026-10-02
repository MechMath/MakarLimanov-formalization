import MakarLimanov.Compression
import Mathlib.Data.Matrix.Mul

/-!
# Shift and diagonal word separation

A word is encoded by its number of `false` letters together with the number of `true`
letters at each shift level.  Distinct words have distinct codes.  This is the
combinatorial ingredient of the matrix model in equation (3.2) of the paper.
-/

namespace MakarLimanov.WordSeparation

open Matrix

noncomputable section

/-- The number of shift letters in a word. -/
def shifts : List Bool → ℕ
  | [] => 0
  | false :: w => shifts w + 1
  | true :: w => shifts w

/-- Exponents of the independent diagonal variables, in right-to-left action order. -/
def exponents : List Bool → (ℕ →₀ ℕ)
  | [] => 0
  | false :: w => exponents w
  | true :: w => exponents w + Finsupp.single (shifts w) 1

@[simp] theorem shifts_nil : shifts [] = 0 := rfl
@[simp] theorem shifts_false (w : List Bool) : shifts (false :: w) = shifts w + 1 := rfl
@[simp] theorem shifts_true (w : List Bool) : shifts (true :: w) = shifts w := rfl
@[simp] theorem exponents_nil : exponents [] = 0 := rfl
@[simp] theorem exponents_false (w : List Bool) : exponents (false :: w) = exponents w := rfl
@[simp] theorem exponents_true (w : List Bool) :
    exponents (true :: w) = exponents w + Finsupp.single (shifts w) 1 := rfl

/-- A word never visits a level above its total number of shifts. -/
theorem exponents_above (w : List Bool) (n : ℕ) (hn : shifts w < n) :
    exponents w n = 0 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · exact ih (by simpa using Nat.lt_of_succ_lt hn)
    · simp only [shifts_true] at hn
      simp [ih hn, ne_of_lt hn]

/-- Shift number and diagonal exponents together recover the complete ordered word. -/
theorem code_injective : Function.Injective (fun w : List Bool ↦ (shifts w, exponents w)) := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v =>
      have hc := congrArg Prod.fst h
      have he := congrArg Prod.snd h
      cases b
      · simp at hc
      · have he' := congrArg (fun c : ℕ →₀ ℕ ↦ c (shifts v)) he
        simp at he'
  | cons b u ih =>
    intro v h
    cases v with
    | nil =>
      have hc := congrArg Prod.fst h
      have he := congrArg Prod.snd h
      cases b
      · simp at hc
      · have he' := congrArg (fun c : ℕ →₀ ℕ ↦ c (shifts u)) he
        simp at he'
    | cons c v =>
      have hc := congrArg Prod.fst h
      have he := congrArg Prod.snd h
      dsimp only at hc he
      cases b <;> cases c
      · congr 1
        apply ih
        exact Prod.ext (by simpa using hc) he
      · have ha : shifts u < shifts v := by simp only [shifts_false, shifts_true] at hc; omega
        have he' := congrArg (fun e : ℕ →₀ ℕ ↦ e (shifts v)) he
        simp [exponents_above u _ ha] at he'
      · have ha : shifts v < shifts u := by simp only [shifts_false, shifts_true] at hc; omega
        have he' := congrArg (fun e : ℕ →₀ ℕ ↦ e (shifts u)) he
        simp [exponents_above v _ ha] at he'
      · congr 1
        apply ih
        simp only [shifts_true] at hc
        simp only [exponents_true, hc, add_left_inj] at he
        exact Prod.ext hc he

/-- Restrict the exponent code to the finite set of levels used by a bounded word. -/
def finiteExponents (A : ℕ) (w : List Bool) : Fin (A + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ exponents w i.val)

@[simp] theorem finiteExponents_apply (A : ℕ) (w : List Bool) (i : Fin (A + 1)) :
    finiteExponents A w i = exponents w i.val := rfl

/-- Finite exponent codes still distinguish all words with at most `A` shifts. -/
theorem finiteCode_injective {A : ℕ} {u v : List Bool}
    (hu : shifts u ≤ A) (hv : shifts v ≤ A)
    (hc : shifts u = shifts v) (he : finiteExponents A u = finiteExponents A v) : u = v := by
  apply code_injective
  refine Prod.ext hc ?_
  ext n
  by_cases hn : n ≤ A
  · exact congrArg (fun e : Fin (A + 1) →₀ ℕ ↦ e ⟨n, by omega⟩) he
  · rw [exponents_above u n (hu.trans_lt (lt_of_not_ge hn)),
      exponents_above v n (hv.trans_lt (lt_of_not_ge hn))]

@[simp] theorem finiteExponents_nil (A : ℕ) : finiteExponents A [] = 0 := by
  ext i
  simp

@[simp] theorem finiteExponents_false (A : ℕ) (w : List Bool) :
    finiteExponents A (false :: w) = finiteExponents A w := by
  ext i
  simp

theorem finiteExponents_true (A : ℕ) (w : List Bool) (hw : shifts w ≤ A) :
    finiteExponents A (true :: w) =
      finiteExponents A w + Finsupp.single ⟨shifts w, by omega⟩ 1 := by
  ext i
  simp [Finsupp.single_apply, Fin.ext_iff]

variable {k : Type*} [CommRing k]

/-- The shift to the next basis vector, truncated above level `A`. -/
def shiftMatrix (A : ℕ) : Matrix (Fin (A + 1)) (Fin (A + 1))
    (MvPolynomial (Fin (A + 1)) k) :=
  fun i j ↦ if i.val = j.val + 1 then 1 else 0

/-- Independent diagonal entries at every level. -/
def diagonalMatrix (A : ℕ) : Matrix (Fin (A + 1)) (Fin (A + 1))
    (MvPolynomial (Fin (A + 1)) k) := Matrix.diagonal MvPolynomial.X

/-- The ordered matrix product associated to a binary word. -/
def wordMatrix (A : ℕ) (w : List Bool) : Matrix (Fin (A + 1)) (Fin (A + 1))
    (MvPolynomial (Fin (A + 1)) k) :=
  (w.map (fun b : Bool ↦ if b then diagonalMatrix (k := k) A else shiftMatrix A)).prod

theorem shiftMatrix_single (A : ℕ) (j : Fin (A + 1)) (hj : j.val < A)
    (c : MvPolynomial (Fin (A + 1)) k) :
    shiftMatrix A *ᵥ Pi.single j c = Pi.single ⟨j.val + 1, by omega⟩ c := by
  rw [Matrix.mulVec_single]
  ext i
  simp [shiftMatrix, Matrix.col_apply, Pi.single_apply, Fin.ext_iff]

theorem diagonalMatrix_single (A : ℕ) (j : Fin (A + 1))
    (c : MvPolynomial (Fin (A + 1)) k) :
    diagonalMatrix A *ᵥ Pi.single j c = Pi.single j (MvPolynomial.X j * c) := by
  exact Matrix.diagonal_mulVec_single _ _ _

/-- Equation (3.2), using the reversed numbering of the finite basis. -/
theorem wordMatrix_action (A : ℕ) (w : List Bool) (hw : shifts w ≤ A) :
    wordMatrix (k := k) A w *ᵥ Pi.single 0 1 =
      Pi.single (⟨shifts w, by omega⟩ : Fin (A + 1))
        (MvPolynomial.monomial (finiteExponents A w) (1 : k)) := by
  induction w with
  | nil =>
    change (1 : Matrix (Fin (A + 1)) (Fin (A + 1)) _) *ᵥ _ = _
    rw [Matrix.one_mulVec]
    simp
  | cons b w ih =>
    cases b
    · have hw' : shifts w < A := by simpa using Nat.lt_of_succ_le hw
      simp only [wordMatrix, List.map_cons, Bool.false_eq_true, ↓reduceIte, List.prod_cons,
        ← Matrix.mulVec_mulVec]
      change shiftMatrix A *ᵥ (wordMatrix A w *ᵥ Pi.single 0 1) = _
      rw [ih hw'.le, shiftMatrix_single A _ hw']
      simp only [shifts_false, finiteExponents_false]
    · simp only [shifts_true] at hw
      simp only [wordMatrix, List.map_cons, ↓reduceIte, List.prod_cons,
        ← Matrix.mulVec_mulVec]
      change diagonalMatrix A *ᵥ (wordMatrix A w *ᵥ Pi.single 0 1) = _
      rw [ih hw, diagonalMatrix_single, finiteExponents_true A w hw]
      congr 1
      rw [add_comm (finiteExponents A w) (Finsupp.single _ _),
        MvPolynomial.monomial_single_add]
      simp

/-- The only potentially occupied entry in the initial column is the encoded monomial. -/
theorem wordMatrix_entry (A : ℕ) (w : List Bool) (hw : shifts w ≤ A)
    (i : Fin (A + 1)) :
    wordMatrix (k := k) A w i 0 =
      if shifts w = i.val then MvPolynomial.monomial (finiteExponents A w) 1 else 0 := by
  have hh := congrFun (wordMatrix_action (k := k) A w hw) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Fin.ext_iff, eq_comm] using hh

/-- Extracting a word code from a matrix word returns the Kronecker delta. -/
theorem wordMatrix_coefficient (A : ℕ) (u v : List Bool)
    (hu : shifts u ≤ A) (hv : shifts v ≤ A) :
    MvPolynomial.coeff (finiteExponents A u)
      (wordMatrix (k := k) A v ⟨shifts u, by omega⟩ 0) = if u = v then 1 else 0 := by
  rw [wordMatrix_entry A v hv]
  by_cases huv : u = v
  · subst v
    simp
  · by_cases hc : shifts v = shifts u
    · have he : finiteExponents A v ≠ finiteExponents A u := by
        intro h
        exact huv (finiteCode_injective hu hv hc.symm h.symm)
      simp [huv, hc, he]
    · simp [huv, hc]

open ControlledMatrix

/-- Recover any occupied word coefficient from the finite shift/diagonal evaluation. -/
theorem evaluation_coefficient (A : ℕ) (f : FreeAlgebra k Bool)
    (hA : ∀ v ∈ (wordCoefficients f).support, shifts v.toList ≤ A)
    (w : FreeMonoid Bool) (hw : shifts w.toList ≤ A) :
    MvPolynomial.coeff (finiteExponents A w.toList)
      ((FreeAlgebra.lift k
        (fun b : Bool ↦ if b then diagonalMatrix (k := k) A else shiftMatrix A) f)
        ⟨shifts w.toList, by omega⟩ 0) = wordCoefficients f w := by
  classical
  rw [lift_eq_word_sum]
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul]
  have he (v : FreeMonoid Bool) (hv : v ∈ (wordCoefficients f).support) :
      (wordCoefficients f v) •
        MvPolynomial.coeff (finiteExponents A w.toList)
          ((v.toList.map
            (fun b : Bool ↦ if b then diagonalMatrix (k := k) A else shiftMatrix A)).prod
            ⟨shifts w.toList, by omega⟩ 0) =
        if v = w then wordCoefficients f w else 0 := by
    change (wordCoefficients f v) •
      MvPolynomial.coeff (finiteExponents A w.toList)
        (wordMatrix A v.toList ⟨shifts w.toList, by omega⟩ 0) = _
    rw [wordMatrix_coefficient A w.toList v.toList hw (hA v hv)]
    by_cases hvw : v = w
    · subst v
      simp
    · have hl : w.toList ≠ v.toList := fun h ↦ hvw (FreeMonoid.toList.injective h).symm
      simp [hvw, hl]
  rw [Finset.sum_congr rfl he]
  by_cases hw' : w ∈ (wordCoefficients f).support
  · simp [hw']
  · simp [Finsupp.notMem_support_iff.mp hw']

/-- Every nonzero polynomial of bounded shift degree has a nonzero finite matrix value. -/
theorem evaluation_ne_zero (A : ℕ) (f : FreeAlgebra k Bool) (hf : f ≠ 0)
    (hA : ∀ v ∈ (wordCoefficients f).support, shifts v.toList ≤ A) :
    FreeAlgebra.lift k
      (fun b : Bool ↦ if b then diagonalMatrix (k := k) A else shiftMatrix A) f ≠ 0 := by
  classical
  have hc : wordCoefficients f ≠ 0 := by
    intro hh
    apply hf
    exact FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective (by simpa [wordCoefficients] using hh)
  obtain ⟨w, hw⟩ := Finsupp.ne_iff.mp hc
  have hw' : w ∈ (wordCoefficients f).support := Finsupp.mem_support_iff.mpr hw
  intro hz
  have he := evaluation_coefficient A f hA w (hA w hw')
  rw [hz] at he
  simp at he
  exact hw he.symm

/-- Every nonzero binary free polynomial has an explicit finite shift/diagonal witness. -/
theorem exists_evaluation_ne_zero (f : FreeAlgebra k Bool) (hf : f ≠ 0) :
    ∃ A : ℕ, FreeAlgebra.lift k
      (fun b : Bool ↦ if b then diagonalMatrix (k := k) A else shiftMatrix A) f ≠ 0 := by
  classical
  refine ⟨(wordCoefficients f).support.sup (fun w ↦ shifts w.toList), ?_⟩
  apply evaluation_ne_zero _ f hf
  intro w hw
  exact Finset.le_sup hw

end

end MakarLimanov.WordSeparation
