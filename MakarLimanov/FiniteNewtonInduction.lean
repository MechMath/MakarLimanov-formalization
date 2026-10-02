import MakarLimanov.GeneralNewtonRoot
import MakarLimanov.NewtonResidual
import MakarLimanov.VariationHomogeneity
import MakarLimanov.NewtonConstruction

/-!
# A certified Newton stage

This file isolates the part of the finite Newton argument which is already
kernel checked: a nonconstant, nonzero universal leading coefficient has a
root in a commuting differential extension, and that root cancels the next
Laurent coefficient.  The statement is deliberately formulated for one
stage; it is useful when assembling the finite induction without hiding a
stage construction behind an axiom.
-/

noncomputable section

namespace MakarLimanov.FiniteNewtonInduction

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open DifferentialCoefficients SymbolSpecialization
open GenericJets JetPolynomialCoefficients JetSpecialization
open VariationCoefficients

universe u

/-! ### Finite assembly of certified stages

The algebraic part of a Newton step changes the coefficient field, so it is
awkward to package a whole run as a single structure carrying one fixed field.
The following small recursion lemma is the field-independent assembly layer.
It is deliberately stated for an arbitrary invariant: all mathematical content
about a particular Newton correction belongs in the step theorem supplied to
`iterate_invariant`.  The lemma itself is constructive (apart from the
ambient `noncomputable` section) and introduces no choice of a new axiom.
-/

theorem iterate_invariant {S : Type*} (Inv : ℕ → S → Prop)
    (step : ∀ (i : ℕ) (s : S), Inv i s → ∃ t : S, Inv (i + 1) t)
    (n : ℕ) (s₀ : S) (hs₀ : Inv 0 s₀) :
    ∃ sₙ : S, Inv n sₙ := by
  induction n generalizing s₀ with
  | zero => exact ⟨s₀, hs₀⟩
  | succ n ih =>
      obtain ⟨sₙ, hsₙ⟩ := ih s₀ hs₀
      obtain ⟨t, ht⟩ := step n sₙ hsₙ
      exact ⟨t, by simpa [Nat.succ_eq_add_one] using ht⟩

/- A dependent version is the one used when a Newton correction enlarges the
coefficient field.  `State i` may therefore carry a different field and
different derivations at every stage; the only shared datum is the invariant.
-/
theorem iterate_dependent_invariant {State : ℕ → Type*}
    (Inv : ∀ i, State i → Prop)
    (step : ∀ (i : ℕ) (s : State i), Inv i s →
      ∃ t : State (i + 1), Inv (i + 1) t)
    (n : ℕ) (s₀ : State 0) (hs₀ : Inv 0 s₀) :
    ∃ sₙ : State n, Inv n sₙ := by
  induction n generalizing s₀ with
  | zero => exact ⟨s₀, hs₀⟩
  | succ n ih =>
      obtain ⟨sₙ, hsₙ⟩ := ih s₀ hs₀
      obtain ⟨t, ht⟩ := step n sₙ hsₙ
      exact ⟨t, by simpa [Nat.succ_eq_add_one] using ht⟩


variable {k F E : Type u} [Field k] [Field F] [Field E]
  [CharZero k] [CharZero F] [CharZero E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/- A nonzero positive-degree homogeneous universal coefficient is automatically
nonunit.  This is the algebraic fact needed to feed a variation coefficient
into `corrected_stage`. -/
theorem homogeneous_nonunit {σ R : Type*} [Field R] {P : MvPolynomial σ R}
    {j : ℕ} (hj : 0 < j) (hhom : P.IsHomogeneous j) (hP : P ≠ 0) :
    ¬ IsUnit P := by
  intro hunit
  have hdeg : P.totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have hhomdeg : P.totalDegree = j := hhom.totalDegree hP
  omega

/-- A homogeneous polynomial of degree divisible by `e` has support only in
monomials whose total exponent is divisible by `e`. -/
theorem homogeneous_support_divisible {σ R : Type*} [Field R]
    {P : MvPolynomial σ R} {j e : ℕ} (hhom : P.IsHomogeneous j)
    (he : e ∣ j) : ∀ d ∈ P.support, e ∣ d.sum (fun _ n ↦ n) := by
  intro d hd
  change e ∣ ∑ i ∈ d.support, d i
  rw [← hhom.degree_eq_sum_deg_support hd]
  exact he

/-- A nonzero positive variation coefficient has a canonical nonunit
representative in the generic jet polynomial ring. -/
theorem variation_coefficient_representative
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ) (hj : 0 < j)
    (hcoef : (genericVariation (E := E) δ η hc p hp q z f j).coeff n ≠ 0) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P.IsHomogeneous j ∧ P ≠ 0 ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericVariation (E := E) δ η hc p hp q z f j).coeff n ∧
      ¬ IsUnit P := by
  obtain ⟨P, hhom, hmap, hspecial⟩ :=
    VariationHomogeneity.exists_homogeneous_universal_variation_coefficient
      (E := E) (G := E) δ η hc p hp q z f j n
  have hP : P ≠ 0 := by
    intro hzero
    apply hcoef
    rw [← hmap, hzero, map_zero]
  exact ⟨P, hhom, hP, hmap, homogeneous_nonunit (σ := ℕ × ℕ) (R := F)
    hj hhom hP⟩

/-- One genuine Newton correction from a universal nonconstant leading
coefficient.  The coefficient representative `P` is obtained from
`exists_universal_residual_coefficient`; the only hypotheses specific to the
current stage are that it is nonzero and nonunit. -/
theorem corrected_stage
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hPn : P ≠ 0) (hPnu : ¬ IsUnit P) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G) (_ : Algebra F G)
      (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  obtain ⟨m, hm, G, hG, hKG, hFG, hKF, D, H, w, hDH, hD, hH, hroot, hlow, htop⟩ :=
    GeneralNewtonRoot.exists_polynomial_step P hPnu hPn δ η hc
  letI : Field G := hG
  letI : Algebra k G := hKG
  letI : Algebra F G := hFG
  letI : IsScalarTower k F G := hKF
  let hCG : CharZero G := charZero_of_injective_algebraMap (algebraMap F G).injective
  letI : CharZero G := hCG
  refine ⟨G, hG, hCG, hKG, hFG, hKF, D, H, w, hDH, hD, hH, ?_⟩
  have hroot' : MvPolynomial.aeval
      (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P = 0 := by
    exact hroot
  have hstep := NewtonResidual.corrected_symbol_of_root
      (E := E) (G := G) δ η hc p hp q z D H hDH hD hH w f b r hz hb hq hr P hP hroot'
  exact hstep

/-- If the universal coefficient at the current residual index vanishes, no
extension or correction is needed: the Laurent lower bound advances directly.
This is the zero branch of the stage dichotomy. -/
theorem zero_coefficient_progress
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hr : LowerBound r (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hP0 : P = 0) :
    LowerBound (r + 1) (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f) := by
  apply NewtonResidual.lowerBound_succ_of_coeff_eq_zero _ r hr
  rw [← hP, hP0, map_zero]

/-- Stage dichotomy for a positive homogeneous leading representative.  The
zero representative advances the support bound directly; a nonzero one is
automatically nonunit and therefore produces the genuine differential Newton
extension from `corrected_stage`. -/
theorem stage_dichotomy
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ) (j : ℕ) (hj : 0 < j)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f))
    (hrep : ∃ P : MvPolynomial (ℕ × ℕ) F,
      P.IsHomogeneous j ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f).coeff r) :
    LowerBound (r + 1) (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f) ∨
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G) (_ : Algebra F G)
      (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  obtain ⟨P, hhom, hP⟩ := hrep
  by_cases hP0 : P = 0
  · exact Or.inl (zero_coefficient_progress δ η hc p hp q z f r hr P hP hP0)
  · exact Or.inr (corrected_stage δ η hc p hp q z f b r hz hb hq hr P hP hP0
      (homogeneous_nonunit hj hhom hP0))

/-- Arithmetic bridge from the multiplicity budget produced by a Newton stage
to the lattice termination theorem. -/
theorem termination_of_multiplicity_budget {M T : ℕ}
    (hM : 0 < M) (r : ℕ → ℤ) (p e m : ℕ → ℕ)
    (hzero : 0 ≤ (r 0 : ℤ)) (hp : ∀ j, 0 < p j) (he : ∀ j, 0 < e j)
    (hm : ∀ j, 0 < m j)
    (hbudget : ∀ j, p j * e j * m j ≤ M)
    (hnext : ∀ j < M * T, p (j + 1) = p j * e j)
    (hr : ∀ j < M * T, (r j : ℤ) * (e j : ℤ) < r (j + 1)) :
    (T : ℚ) ≤ (r (M * T) : ℚ) / p (M * T) := by
  apply newton_termination_of_lattice hM r p e hzero hp he ?_ hnext hr
  intro j
  apply denominator_bound (Nat.mul_pos (he j) (hm j))
  calc
    p j * (e j * m j) = p j * e j * m j := by ring
    _ ≤ M := hbudget j

end MakarLimanov.FiniteNewtonInduction
