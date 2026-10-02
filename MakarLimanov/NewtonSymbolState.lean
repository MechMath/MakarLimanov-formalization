import MakarLimanov.FiniteNewtonRun
import MakarLimanov.SymbolReindex
import MakarLimanov.BudgetedNewtonStep
import MakarLimanov.CorrectedNextSlope

/-!
# Finite assembly of concrete Newton symbols

A state packages its own coefficient field, commuting derivations, and finite
Laurent symbol.  Its residual bound is an integer on the current lattice.  A
local correction is required only before the requested precision is reached;
finite induction then extracts an actual symbol approximation.
-/

noncomputable section

namespace MakarLimanov.NewtonSymbolState

open SymbolSeries SymbolSeries.StarSeries ControlledMatrix

universe u

variable {K : Type u} [Field K]

/-- The algebraic and numerical invariant at one concrete Newton stage. -/
structure State (g : FreeAlgebra K Bool) (A : ℕ) where
  F : Type u
  [field : Field F]
  [algebra : Algebra K F]
  [charZero : CharZero F]
  p : ℕ
  positive_p : 0 < p
  b : ℕ
  positive_b : 0 < b
  budget : p * b ≤ wordDegree g
  r : ℤ
  δ : Derivation K F F
  η : Derivation K F F
  commute : Function.Commute δ η
  Z : LaurentSeries F
  finite_support : Z.support.Finite
  symbol_bound : LowerBound (-(p * A : ℤ)) Z
  residual_bound : LowerBound r
    (toSeries (evaluateAt (hp := positive_p) (h := commute) Z (1 + g)))

attribute [instance] State.field State.algebra State.charZero

namespace State

variable {g : FreeAlgebra K Bool} {A : ℕ}

/-- The zero symbol supplies the initial state for every chosen support bound. -/
def initial [CharZero K] (g : FreeAlgebra K Bool) (hg : g ≠ 0)
    (hab : binaryAbelianize K g = 0) (A : ℕ) : State g A where
  F := K
  field := inferInstance
  algebra := inferInstance
  charZero := inferInstance
  p := 1
  positive_p := by decide
  b := wordDegree g
  positive_b := by
    have h := BinarySupport.wordDegree_ge_two_of_abelianize_zero g hg hab
    omega
  budget := by simp
  r := 0
  δ := 0
  η := 0
  commute := fun _ ↦ rfl
  Z := 0
  finite_support := by simp
  symbol_bound := by
    intro n hn
    exact HahnSeries.coeff_zero
  residual_bound :=
    (InitialNewton.initial_stage_data g hab 1 (by decide) 0 0 (fun _ ↦ rfl)).2.2

/-- Residual precision in the unramified coordinate. -/
def precision (S : State g A) : ℚ := (S.r : ℚ) / S.p

@[simp] theorem initial_precision [CharZero K] (g : FreeAlgebra K Bool)
    (hg : g ≠ 0) (hab : binaryAbelianize K g = 0) (A : ℕ) :
    (initial g hg hab A).precision = 0 := by
  simp [precision, initial]

theorem denominator_le_degree (S : State g A) : S.p ≤ wordDegree g :=
  denominator_bound S.positive_b S.budget

theorem positive_degree (S : State g A) : 0 < wordDegree g :=
  lt_of_lt_of_le S.positive_p S.denominator_le_degree

/-- Replace the certified residual lower bound by its actual Laurent order.
The coefficient field, symbol, denominator, and multiplicity budget are unchanged. -/
def exactOrder (S : State g A) : State g A :=
  { S with
    r := (toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g))).order
    residual_bound := lowerBound_order _ }

theorem le_exactOrder (S : State g A)
    (hres : toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g)) ≠ 0) : S.r ≤ S.exactOrder.r :=
  (HahnSeries.le_order_iff_forall hres).mpr S.residual_bound

theorem precision_le_exactOrder (S : State g A)
    (hres : toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g)) ≠ 0) : S.precision ≤ S.exactOrder.precision := by
  have hr : (S.r : ℚ) ≤ S.exactOrder.r := by exact_mod_cast S.le_exactOrder hres
  exact div_le_div_of_nonneg_right hr (by positivity)

theorem exactOrder_coefficient_ne_zero (S : State g A)
    (hres : toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g)) ≠ 0) :
    (toSeries (evaluateAt (hp := S.exactOrder.positive_p) (h := S.exactOrder.commute)
      S.exactOrder.Z (1 + g))).coeff S.exactOrder.r ≠ 0 :=
  (HahnSeries.coeff_order_eq_zero.not).mpr hres

@[simp] theorem exactOrder_idempotent (S : State g A) :
    S.exactOrder.exactOrder = S.exactOrder := rfl

/-- Lattice refinement transports a state exactly.  The new positive degree
budget is supplied by the multiplicity estimate for the chosen Newton factor. -/
def refine (S : State g A) (e m : ℕ) (he : 0 < e) (hm : 0 < m)
    (hbudget : e * m ≤ S.b) : State g A where
  F := S.F
  field := S.field
  algebra := S.algebra
  charZero := S.charZero
  p := S.p * e
  positive_p := Nat.mul_pos S.positive_p he
  b := m
  positive_b := hm
  budget := newton_budget hbudget le_rfl S.budget
  r := (e : ℤ) * S.r
  δ := S.δ
  η := S.η
  commute := S.commute
  Z := refineLattice e he S.Z
  finite_support := finite_support_refineLattice e he S.Z S.finite_support
  symbol_bound := by
    have h := (lowerBound_refineLattice_iff e he (-(S.p * A : ℤ)) S.Z).mpr
      S.symbol_bound
    convert h using 1
    push_cast
    ring
  residual_bound :=
    (lowerBound_refineLattice_evaluateAt_iff S.p e S.positive_p he
      S.δ S.η S.commute S.Z (1 + g) S.r).mpr S.residual_bound

/-- Refinement changes the lattice indices but preserves normalized precision. -/
@[simp] theorem precision_refine (S : State g A) (e m : ℕ) (he : 0 < e) (hm : 0 < m)
    (hbudget : e * m ≤ S.b) :
    (S.refine e m he hm hbudget).precision = S.precision := by
  have hp : (S.p : ℚ) ≠ 0 := by exact_mod_cast S.positive_p.ne'
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  dsimp [refine, precision]
  push_cast
  field_simp

/-- The integer residual bound yields the requested terminal residual bound. -/
def terminal (S : State g A) (T : ℕ) (hT : (T : ℚ) ≤ S.precision) :
    FiniteNewtonApproximation.TerminalData g A T where
  F := S.F
  field := S.field
  algebra := S.algebra
  charZero := S.charZero
  p := S.p
  hp := S.positive_p
  denominator_bound := S.denominator_le_degree
  δ := S.δ
  η := S.η
  commute := S.commute
  Z := S.Z
  finite_support := S.finite_support
  symbol_bound := S.symbol_bound
  residual_bound := by
    apply S.residual_bound.mono
    have hp : (0 : ℚ) < S.p := by exact_mod_cast S.positive_p
    have h := (le_div_iff₀ hp).mp hT
    have h' : (S.p : ℚ) * T ≤ S.r := by simpa [mul_comm] using h
    exact_mod_cast h'

/-- A genuine correction refines the lattice and strictly raises its residual index. -/
def Step (S S' : State g A) : Prop :=
  ∃ e : ℕ, 0 < e ∧ S'.p = S.p * e ∧ S.r * (e : ℤ) < S'.r

/-- After a genuine correction, replacing its lower bound by the actual
nonzero residual order preserves the strict step relation. -/
theorem Step.exactOrder {S S' : State g A} (hstep : S.Step S')
    (hres : toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
      S'.Z (1 + g)) ≠ 0) : S.Step S'.exactOrder := by
  obtain ⟨e, he, hp, hr⟩ := hstep
  exact ⟨e, he, hp, hr.trans_le (S'.le_exactOrder hres)⟩

/-- A zero coefficient at the current residual index advances the state on
the existing field and lattice, without selecting a differential root. -/
def advance (S : State g A)
    (hzero : (toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g))).coeff S.r = 0) : State g A :=
  { S with
    r := S.r + 1
    residual_bound :=
      NewtonResidual.lowerBound_succ_of_coeff_eq_zero _ S.r S.residual_bound hzero }

theorem step_advance (S : State g A)
    (hzero : (toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g))).coeff S.r = 0) : S.Step (S.advance hzero) := by
  exact ⟨1, by decide, by simp [advance], by simp [advance]⟩

/-- A correction after refinement is a genuine correction of the original state. -/
theorem Step.of_refine {S S' : State g A} (e m : ℕ) (he : 0 < e) (hm : 0 < m)
    (hbudget : e * m ≤ S.b) (hstep : (S.refine e m he hm hbudget).Step S') :
    S.Step S' := by
  obtain ⟨d, hd, hp, hr⟩ := hstep
  refine ⟨e * d, Nat.mul_pos he hd, ?_, ?_⟩
  · simpa only [refine, Nat.mul_assoc] using hp
  · have hr' : ((e : ℤ) * S.r) * (d : ℤ) < S'.r := hr
    convert hr' using 1
    push_cast
    ring

theorem Step.progress {S S' : State g A} (hstep : S.Step S') :
    S.precision + 1 / (wordDegree g : ℚ) ≤ S'.precision := by
  obtain ⟨e, he, hp, hr⟩ := hstep
  have hbudget : S.p * e ≤ wordDegree g := by
    rw [← hp]
    exact S'.denominator_le_degree
  simpa only [precision, hp] using
    newton_lattice_progress S.positive_p he hbudget hr

/-- The data retained by a ramified correction, including the polynomial and
root whose translated multiplicity is the next state's degree budget. -/
structure RefinedCorrection (S S' : State g A) (e : ℕ) (q : ℤ) where
  positive_factor : 0 < e
  [algebra : Algebra S.F S'.F]
  [tower : IsScalarTower K S.F S'.F]
  polynomial : MvPolynomial (ℕ × ℕ) S.F
  correction : S'.F
  denominator_eq : S'.p = S.p * e
  refinement_budget : e * S'.b ≤ S.b
  residual_index_eq : S'.r = (e : ℤ) * S.r + 1
  delta_extension : ∀ a : S.F,
    S'.δ (algebraMap S.F S'.F a) = algebraMap S.F S'.F (S.δ a)
  eta_extension : ∀ a : S.F,
    S'.η (algebraMap S.F S'.F a) = algebraMap S.F S'.F (S.η a)
  symbol_eq : S'.Z =
    mapField (IsScalarTower.toAlgHom K S.F S'.F)
      (refineLattice e positive_factor S.Z) + HahnSeries.single q correction
  polynomial_map :
    algebraMap (MvPolynomial (ℕ × ℕ) S.F) (FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      polynomial =
      (NewtonResidual.genericResidual
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p positive_factor)
        q (refineLattice e positive_factor S.Z) (1 + g)).coeff ((e : ℤ) * S.r)
  translated_lowest :
    let jets : ℕ × ℕ → S'.F := fun ij ↦ S'.δ^[ij.1] (S'.η^[ij.2] correction)
    let translated :=
      NewtonTranslation.translate jets (MvPolynomial.map (algebraMap S.F S'.F) polynomial)
    (∀ j < S'.b, MvPolynomial.homogeneousComponent j translated = 0) ∧
      MvPolynomial.homogeneousComponent S'.b translated ≠ 0

attribute [instance] RefinedCorrection.algebra RefinedCorrection.tower

theorem RefinedCorrection.step {S S' : State g A} {e : ℕ} {q : ℤ}
    (C : RefinedCorrection S S' e q) : S.Step S' := by
  refine ⟨e, C.positive_factor, C.denominator_eq, ?_⟩
  rw [C.residual_index_eq, mul_comm S.r]
  omega

set_option maxHeartbeats 1000000

/-- A nonzero corrected residual determines the next supporting slope from a
refined Newton correction. The only stage-specific input is the generic
residual lower bound at the slope used by this correction. -/
theorem RefinedCorrection.nextSupportingSlope [CharZero K]
    {S S' : State g A} {e : ℕ} {q : ℤ}
    (C : RefinedCorrection S S' e q)
    (hr : LowerBound ((e : ℤ) * S.r)
      (NewtonResidual.genericResidual
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p C.positive_factor)
        q (refineLattice e C.positive_factor S.Z) (1 + g)))
    (hnew : toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
      S'.Z (1 + g)) ≠ 0) :
    ∃ (active : Finset ℕ) (s' : ℚ) (j : ℕ),
      (∀ i, i ∈ active ↔ i ≤ ControlledMatrix.wordDegree (1 + g) ∧ 0 < i ∧
        VariationCoefficients.genericVariation
          (E := FractionRing (MvPolynomial (ℕ × ℕ) S'.F))
          S'.δ S'.η S'.commute S'.p S'.positive_p 0 S'.Z (1 + g) i ≠ 0) ∧
      j ∈ active ∧ 0 < j ∧ j ≤ S'.b ∧
      (q : ℚ) < s' ∧
      ((VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S'.F))
        S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g) j).order : ℚ) +
          (j : ℚ) * (s' - (q : ℚ)) =
        ((toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
          S'.Z (1 + g))).order : ℚ) ∧
      (∀ i ∈ active,
        ((toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
          S'.Z (1 + g))).order : ℚ) ≤
          ((VariationCoefficients.genericVariation
            (E := FractionRing (MvPolynomial (ℕ × ℕ) S'.F))
            S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g) i).order : ℚ) +
            (i : ℚ) * (s' - (q : ℚ))) ∧
      (∀ i ∈ active,
        ((VariationCoefficients.genericVariation
          (E := FractionRing (MvPolynomial (ℕ × ℕ) S'.F))
          S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g) i).order : ℚ) +
            (i : ℚ) * (s' - (q : ℚ)) =
          ((toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
            S'.Z (1 + g))).order : ℚ) → i ≤ S'.b) := by
  classical
  letI : Algebra S.F S'.F := C.algebra
  letI : IsScalarTower K S.F S'.F := C.tower
  let E := FractionRing (MvPolynomial (ℕ × ℕ) S.F)
  let J := FractionRing (MvPolynomial (ℕ × ℕ) S'.F)
  let z : LaurentSeries S.F := refineLattice e C.positive_factor S.Z
  let newResidual : LaurentSeries S'.F :=
    toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute) S'.Z (1 + g))
  have hr' : LowerBound ((e : ℤ) * S.r)
      (NewtonResidual.genericResidual
        (E := E) S.δ S.η S.commute S'.p S'.positive_p q z (1 + g)) := by
    simpa only [← C.denominator_eq] using hr
  have hP' :
      algebraMap (MvPolynomial (ℕ × ℕ) S.F) E C.polynomial =
        (NewtonResidual.genericResidual
          (E := E) S.δ S.η S.commute S'.p S'.positive_p q z (1 + g)).coeff
            ((e : ℤ) * S.r) := by
    simpa only [← C.denominator_eq] using C.polynomial_map
  have horder : ((e : ℤ) * S.r) < newResidual.order := by
    have hbound := S'.residual_bound
    have hle : S'.r ≤ newResidual.order :=
      (HahnSeries.le_order_iff_forall hnew).mpr hbound
    dsimp [newResidual]
    rw [C.residual_index_eq] at hle
    exact hle
  have hnewEq : newResidual = toSeries (evaluateAt
      (hp := S'.positive_p)
      (h := S'.commute)
      (mapField (IsScalarTower.toAlgHom K S.F S'.F) z +
        HahnSeries.single q C.correction) (1 + g)) := by
    dsimp [newResidual]
    rw [C.symbol_eq]
  have hresult := CorrectedNextSlope.exists_next_supporting_slope
    (E := E) (K := J) S.δ S.η S.commute S'.p
    S'.positive_p q z (1 + g) ((e : ℤ) * S.r)
    hr' S'.δ S'.η S'.commute C.delta_extension C.eta_extension C.correction
    C.polynomial hP' S'.b S'.positive_b C.translated_lowest.1
    C.translated_lowest.2 newResidual hnewEq hnew horder
  rcases hresult with ⟨_, active, hactive, s', j, hj, hjpos, hjbound,
    hq, heq, hline, htie⟩
  refine ⟨active, s', j, ?_, hj, hjpos, hjbound, hq, ?_, ?_, ?_⟩
  · intro i
    simpa only [C.symbol_eq, z] using hactive i
  · simpa only [C.symbol_eq, newResidual, z] using heq
  · intro i hi
    simpa only [C.symbol_eq, newResidual, z] using hline i hi
  · intro i hi
    simpa only [C.symbol_eq, newResidual, z] using htie i hi

/-- The sparse leading polynomial determines one root, its multiplicity, and
the complete next state on a refined lattice, with all three linked by a
`RefinedCorrection` certificate. -/
theorem exists_refined_correction [CharZero K]
    (S : State g A) (e : ℕ) (he : 0 < e) (q : ℤ)
    (hq : -((S.p * e) * A : ℤ) ≤ q)
    (hr : LowerBound ((e : ℤ) * S.r)
      (NewtonResidual.genericResidual
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
        q (refineLattice e he S.Z) (1 + g)))
    (hres : (toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g))).coeff S.r ≠ 0)
    (hactive : ∃ j : ℕ, 0 < j ∧
      (VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
        q (refineLattice e he S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0)
    (hdiv : ∀ j, (VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
        q (refineLattice e he S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0 → e ∣ j)
    (hdegree : ∀ j, (VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
        q (refineLattice e he S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0 → j ≤ S.b) :
    ∃ S' : State g A, Nonempty (RefinedCorrection S S' e q) := by
  have hfinite := finite_support_refineLattice e he S.Z S.finite_support
  have hsymbol : LowerBound (-((S.p * e) * A : ℤ)) (refineLattice e he S.Z) := by
    have h := (lowerBound_refineLattice_iff e he (-(S.p * A : ℤ)) S.Z).mpr
      S.symbol_bound
    convert h using 1
    ring
  have hres' : (toSeries (evaluateAt (hp := Nat.mul_pos S.positive_p he)
      (h := S.commute) (refineLattice e he S.Z) (1 + g))).coeff ((e : ℤ) * S.r) ≠ 0 := by
    rw [← refineLattice_evaluateAt, refineLattice_coeff]
    exact hres
  obtain ⟨Ψ, m, hΨ, hm, hbudget, G, hG, hCG, hKG, hFG, hKF,
      D, H, w, hDH, hD, hH, hfinite', hsymbol', hresidual', htranslated⟩ :=
    BudgetedNewtonStep.corrected_stage_with_budget
      (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
      q (refineLattice e he S.Z) (1 + g) (-((S.p * e) * A : ℤ))
      ((e : ℤ) * S.r) e S.b he hfinite hsymbol hq hr hres' hactive hdiv hdegree
  letI : Field G := hG
  letI : CharZero G := hCG
  letI : Algebra K G := hKG
  letI : Algebra S.F G := hFG
  letI : IsScalarTower K S.F G := hKF
  let S' : State g A :=
    { F := G
      field := hG
      algebra := hKG
      charZero := hCG
      p := S.p * e
      positive_p := Nat.mul_pos S.positive_p he
      b := m
      positive_b := hm
      budget := newton_budget hbudget le_rfl S.budget
      r := (e : ℤ) * S.r + 1
      δ := D
      η := H
      commute := hDH
      Z := mapField (IsScalarTower.toAlgHom K S.F G)
        (refineLattice e he S.Z) + HahnSeries.single q w
      finite_support := hfinite'
      symbol_bound := hsymbol'
      residual_bound := hresidual' }
  exact ⟨S', ⟨{
    positive_factor := he
    algebra := hFG
    tower := hKF
    polynomial := Ψ
    correction := w
    denominator_eq := rfl
    refinement_budget := hbudget
    residual_index_eq := rfl
    delta_extension := hD
    eta_extension := hH
    symbol_eq := rfl
    polynomial_map := hΨ
    translated_lowest := htranslated }⟩⟩

/-- The certified differential root produces a concrete next state on the
same lattice whenever an admissible integral correction has an active term. -/
theorem step_of_active_variation [CharZero K] (S : State g A) (q : ℤ)
    (hq : -(S.p * A : ℤ) ≤ q)
    (hr : LowerBound S.r
      (NewtonResidual.genericResidual
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute S.p S.positive_p q S.Z (1 + g)))
    (hactive : ∃ j : ℕ, 0 < j ∧
      (VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute S.p S.positive_p q S.Z (1 + g) j).coeff S.r ≠ 0) :
    ∃ S' : State g A, S.Step S' := by
  obtain ⟨G, hG, hCG, hKG, hFG, hKF, D, H, w, hDH, hD, hH,
      hfinite, hsymbol, hresidual⟩ :=
    FiniteNewtonRun.one_step_from_active_variation
      (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      S.δ S.η S.commute S.p S.positive_p q S.Z (1 + g)
      (-(S.p * A : ℤ)) S.r S.finite_support S.symbol_bound hq hr hactive
  letI : Field G := hG
  letI : CharZero G := hCG
  letI : Algebra K G := hKG
  letI : Algebra S.F G := hFG
  letI : IsScalarTower K S.F G := hKF
  let S' : State g A :=
    { F := G
      field := hG
      algebra := hKG
      charZero := hCG
      p := S.p
      positive_p := S.positive_p
      b := S.b
      positive_b := S.positive_b
      budget := S.budget
      r := S.r + 1
      δ := D
      η := H
      commute := hDH
      Z := mapField (IsScalarTower.toAlgHom K S.F G) S.Z + HahnSeries.single q w
      finite_support := hfinite
      symbol_bound := hsymbol
      residual_bound := hresidual }
  exact ⟨S', 1, by decide, by simp [S'], by simp [S']⟩

/-- An active Newton correction on a refined lattice, with the refinement
factor charged to the multiplicity budget, advances the original state. -/
theorem step_of_refined_active_variation [CharZero K]
    (S : State g A) (e m : ℕ) (he : 0 < e) (hm : 0 < m)
    (hbudget : e * m ≤ S.b) (q : ℤ)
    (hq : -((S.p * e) * A : ℤ) ≤ q)
    (hr : LowerBound ((e : ℤ) * S.r)
      (NewtonResidual.genericResidual
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
        q (refineLattice e he S.Z) (1 + g)))
    (hactive : ∃ j : ℕ, 0 < j ∧
      (VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p he)
        q (refineLattice e he S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0) :
    ∃ S' : State g A, S.Step S' := by
  obtain ⟨S', hS'⟩ :=
    step_of_active_variation (S.refine e m he hm hbudget) q hq hr hactive
  exact ⟨S', hS'.of_refine e m he hm hbudget⟩

/-- An identically zero residual can be recorded at any requested precision. -/
def exactTerminal (S : State g A)
    (hzero : toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g)) = 0) (T : ℕ) :
    FiniteNewtonApproximation.TerminalData g A T where
  F := S.F
  field := S.field
  algebra := S.algebra
  charZero := S.charZero
  p := S.p
  hp := S.positive_p
  denominator_bound := S.denominator_le_degree
  δ := S.δ
  η := S.η
  commute := S.commute
  Z := S.Z
  finite_support := S.finite_support
  symbol_bound := S.symbol_bound
  residual_bound := by
    rw [hzero]
    intro n hn
    exact HahnSeries.coeff_zero

/-- A sequence of local corrections reaches precision in at most `degree * T`
steps.  A terminal state is reused without imposing further correction data. -/
theorem exists_precision_state (S₀ : State g A) (hzero : 0 ≤ S₀.precision)
    (T : ℕ)
    (hstep : ∀ S : State g A, S.precision < T → ∃ S', S.Step S') :
    ∃ S : State g A, (T : ℚ) ≤ S.precision := by
  have hM : (0 : ℚ) < wordDegree g := by exact_mod_cast S₀.positive_degree
  have hbound : ∀ n : ℕ, ∃ S : State g A,
      (T : ℚ) ≤ S.precision ∨ (n : ℚ) / wordDegree g ≤ S.precision := by
    intro n
    induction n with
    | zero => exact ⟨S₀, Or.inr (by simpa using hzero)⟩
    | succ n ih =>
      obtain ⟨S, hS⟩ := ih
      by_cases hdone : (T : ℚ) ≤ S.precision
      · exact ⟨S, Or.inl hdone⟩
      · obtain ⟨S', hS'⟩ := hstep S (lt_of_not_ge hdone)
        have hprevious : (n : ℚ) / wordDegree g ≤ S.precision :=
          hS.resolve_left hdone
        refine ⟨S', Or.inr ?_⟩
        have hprogress := hS'.progress
        push_cast
        rw [add_div]
        linarith
  obtain ⟨S, hS⟩ := hbound (wordDegree g * T)
  refine ⟨S, hS.elim id ?_⟩
  simpa only [Nat.cast_mul, mul_div_cancel_left₀ _ (ne_of_gt hM)] using id

/-- Concrete local Newton steps suffice for the finite symbol approximation. -/
theorem approximation_of_steps (S₀ : State g A) (hzero : 0 ≤ S₀.precision)
    (T : ℕ)
    (hstep : ∀ S : State g A, S.precision < T → ∃ S', S.Step S') :
    Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  obtain ⟨S, hS⟩ := exists_precision_state S₀ hzero T hstep
  exact ⟨(S.terminal T hS).toSymbolApproximation⟩

/-- Finite assembly with an additional algebraic invariant.  Only states whose
residual is nonzero and whose precision is insufficient require a next step. -/
theorem approximation_of_nonzero_steps (Inv : State g A → Prop)
    (S₀ : State g A) (hInv₀ : Inv S₀) (hzero : 0 ≤ S₀.precision) (T : ℕ)
    (hstep : ∀ S : State g A, Inv S → S.precision < T →
      toSeries (evaluateAt (hp := S.positive_p) (h := S.commute) S.Z (1 + g)) ≠ 0 →
      ∃ S' : State g A, Inv S' ∧ S.Step S') :
    Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  have hM : (0 : ℚ) < wordDegree g := by exact_mod_cast S₀.positive_degree
  have hbound : ∀ n : ℕ,
      Nonempty (AuditedAssumptions.SymbolApproximation K g A T) ∨
        ∃ S : State g A, Inv S ∧ (n : ℚ) / wordDegree g ≤ S.precision := by
    intro n
    induction n with
    | zero => exact Or.inr ⟨S₀, hInv₀, by simpa using hzero⟩
    | succ n ih =>
      rcases ih with hdone | ⟨S, hInv, hprevious⟩
      · exact Or.inl hdone
      · by_cases hprecision : (T : ℚ) ≤ S.precision
        · exact Or.inl ⟨(S.terminal T hprecision).toSymbolApproximation⟩
        · by_cases hresidual :
            toSeries (evaluateAt (hp := S.positive_p) (h := S.commute) S.Z (1 + g)) = 0
          · exact Or.inl ⟨(S.exactTerminal hresidual T).toSymbolApproximation⟩
          · obtain ⟨S', hInv', hS'⟩ := hstep S hInv (lt_of_not_ge hprecision) hresidual
            refine Or.inr ⟨S', hInv', ?_⟩
            have hprogress := hS'.progress
            push_cast
            rw [add_div]
            linarith
  rcases hbound (wordDegree g * T) with hdone | ⟨S, hInv, hS⟩
  · exact hdone
  · have hprecision : (T : ℚ) ≤ S.precision := by
      simpa only [Nat.cast_mul, mul_div_cancel_left₀ _ (ne_of_gt hM)] using hS
    exact ⟨(S.terminal T hprecision).toSymbolApproximation⟩

/-- A uniform invariant and local nonzero-residual correction are enough for
the complete finite-approximation conclusion, with the support bound fixed
before choosing the target precision. -/
theorem finite_approximation_of_nonzero_steps [CharZero K]
    (g : FreeAlgebra K Bool) (hg : g ≠ 0) (hab : binaryAbelianize K g = 0)
    (A : ℕ) (Inv : State g A → Prop) (hInv : Inv (initial g hg hab A))
    (hstep : ∀ S : State g A, Inv S →
      toSeries (evaluateAt (hp := S.positive_p) (h := S.commute) S.Z (1 + g)) ≠ 0 →
      ∃ S' : State g A, Inv S' ∧ S.Step S') :
    ∀ T : ℕ, Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  intro T
  apply approximation_of_nonzero_steps Inv (initial g hg hab A) hInv (by simp) T
  intro S hS hprecision hresidual
  exact hstep S hS hresidual

end State

end MakarLimanov.NewtonSymbolState
