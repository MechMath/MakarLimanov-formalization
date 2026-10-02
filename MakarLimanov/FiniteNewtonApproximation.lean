import MakarLimanov.FiniteNewtonInduction
import MakarLimanov.NewtonConstruction
import MakarLimanov.SymbolApproximation

/-!
# Finite Newton runs

This file packages the finite bookkeeping that is needed after an individual
Newton correction has been checked.  The coefficient field may change at every
stage, hence the state type is indexed by the stage.  The construction below
does not assert that such a step exists for the symbol problem; it proves that
once a certified step relation is supplied, a coherent run and its endpoint
precision are obtained by ordinary finite recursion.
-/

noncomputable section

namespace MakarLimanov.FiniteNewtonApproximation

universe u

open AuditedAssumptions SymbolSeries SymbolSeries.StarSeries ControlledMatrix

variable {K : Type u} [Field K]

/-! The terminal data are written separately from `SymbolApproximation` so that
the output can be extracted from an invariant at the endpoint of a run. -/

structure TerminalData (g : FreeAlgebra K Bool) (A T : ℕ) where
  F : Type u
  [field : Field F]
  [algebra : Algebra K F]
  [charZero : CharZero F]
  p : ℕ
  hp : 0 < p
  denominator_bound : p ≤ wordDegree g
  δ : Derivation K F F
  η : Derivation K F F
  commute : Function.Commute δ η
  Z : LaurentSeries F
  finite_support : Z.support.Finite
  symbol_bound : LowerBound (-(p * A : ℤ)) Z
  residual_bound : LowerBound (p * T : ℤ)
    (toSeries (evaluateAt (hp := hp) (h := commute) Z (1 + g)))

attribute [instance] TerminalData.field TerminalData.algebra TerminalData.charZero

def TerminalData.toSymbolApproximation {g : FreeAlgebra K Bool} {A T : ℕ}
    (D : TerminalData g A T) : SymbolApproximation K g A T :=
  { F := D.F
    field := D.field
    algebra := D.algebra
    charZero := D.charZero
    p := D.p
    hp := D.hp
    denominator_bound := D.denominator_bound
    δ := D.δ
    η := D.η
    commute := D.commute
    Z := D.Z
    finite_support := D.finite_support
    symbol_bound := D.symbol_bound
    residual_bound := D.residual_bound }

/-- A stage relation carrying the numerical invariants of a Newton run.

`S i` can contain a coefficient field, derivations, a lattice symbol, and a
residual.  `Inv` records the algebraic invariant at that stage.  The relation
only asks for the next state and its one-step precision estimate; all
field-dependent mathematical work is therefore isolated in `step`.
-/
structure RunSpec (M T : ℕ) (S : ℕ → Type u)
    (Inv : ∀ i, S i → Prop) where
  initial : S 0
  initial_inv : Inv 0 initial
  rho : ∀ i, S i → ℚ
  p : ∀ i, S i → ℕ
  b : ∀ i, S i → ℕ
  initial_nonneg : 0 ≤ rho 0 initial
  positive_p : ∀ i s, Inv i s → 0 < p i s
  budget : ∀ i s, Inv i s → p i s * b i s ≤ M
  step : ∀ (i : ℕ) (s : S i), Inv i s →
    ∃ t : S (i + 1), Inv (i + 1) t ∧
      (i < M * T → rho i s + 1 / (M : ℚ) ≤ rho (i + 1) t)

/-- Public name emphasizing that a `RunSpec` is the finite Newton run data. -/
abbrev FiniteNewtonRun := RunSpec

namespace RunSpec

variable {M T : ℕ} {S : ℕ → Type u} {Inv : ∀ i, S i → Prop}
variable (R : RunSpec M T S Inv)

private def run : ∀ i, Subtype (Inv i)
  | 0 => ⟨R.initial, R.initial_inv⟩
  | i + 1 =>
      let h := (run i).property
      let w := Classical.choose (R.step i (run i).val h)
      ⟨w, (Classical.choose_spec (R.step i (run i).val h)).1⟩

private theorem run_step (i : ℕ) :
    Inv (i + 1) (run R (i + 1)).val := by
  exact (run R (i + 1)).property

private theorem run_transition (i : ℕ) :
    ∃ t : S (i + 1), Inv (i + 1) t ∧
      (i < M * T → R.rho i (run R i).val + 1 / (M : ℚ) ≤
        R.rho (i + 1) t) := by
  exact R.step i (run R i).val (run R i).property

def rhoRun (i : ℕ) : ℚ := R.rho i (run R i).val
def pRun (i : ℕ) : ℕ := R.p i (run R i).val
def bRun (i : ℕ) : ℕ := R.b i (run R i).val

theorem rhoRun_zero : rhoRun R 0 = R.rho 0 R.initial := by
  rfl

theorem rhoRun_nonneg : 0 ≤ rhoRun R 0 := by
  simpa [rhoRun] using R.initial_nonneg

theorem pRun_pos (i : ℕ) : 0 < pRun R i := by
  exact R.positive_p i (run R i).val (run R i).property

theorem budgetRun (i : ℕ) : pRun R i * bRun R i ≤ M := by
  exact R.budget i (run R i).val (run R i).property

theorem rhoRun_progress (i : ℕ) (hi : i < M * T) :
    rhoRun R i + 1 / (M : ℚ) ≤ rhoRun R (i + 1) := by
  let hstep := R.step i (run R i).val (run R i).property
  have hprog := (Classical.choose_spec hstep).2
  change R.rho i (run R i).val + 1 / (M : ℚ) ≤
    R.rho (i + 1) (run R (i + 1)).val
  change R.rho i (run R i).val + 1 / (M : ℚ) ≤
    R.rho (i + 1) (Classical.choose
      hstep)
  exact hprog hi

def asNewtonData (R : RunSpec M T S Inv) : NewtonData M T where
  rho := rhoRun R
  p := pRun R
  b := bRun R
  rho_nonneg := rhoRun_nonneg R
  budget := budgetRun R
  progress := rhoRun_progress R

theorem endpoint_precision (hM : 0 < M) :
    (T : ℚ) ≤ rhoRun R (M * T) := by
  exact NewtonData.precision_at_budget (asNewtonData R) hM

theorem endpoint_state (hM : 0 < M) :
    ∃ s : S (M * T), Inv (M * T) s ∧
      (T : ℚ) ≤ R.rho (M * T) s := by
  refine ⟨(run R (M * T)).val, (run R (M * T)).property, ?_⟩
  simpa [rhoRun] using endpoint_precision R hM

end RunSpec

/-- A finite Newton assembly whose invariant contains the actual symbol data.

The `step` field of `run` is the place where one proves a genuine Newton
correction (including extension of the coefficient field and the new residual
lower bound).  `terminal` only extracts the audited symbol fields from the
endpoint invariant; it also receives the endpoint precision proof, so the
output cannot ignore the finite termination argument.
-/
structure AssembledApproximation (g : FreeAlgebra K Bool) (A T : ℕ) where
  positive_degree : 0 < wordDegree g
  State : ℕ → Type u
  Inv : ∀ i, State i → Prop
  run : FiniteNewtonRun (wordDegree g) T State Inv
  terminal : ∀ s : State (wordDegree g * T),
    Inv (wordDegree g * T) s →
      (T : ℚ) ≤ run.rho (wordDegree g * T) s →
      TerminalData g A T

namespace AssembledApproximation

variable {g : FreeAlgebra K Bool} {A T : ℕ}
variable (R : AssembledApproximation g A T)

/-- The endpoint of the certified finite run is an actual symbol approximation. -/
theorem endpoint (R : AssembledApproximation g A T) :
    Nonempty (SymbolApproximation K g A T) := by
  obtain ⟨s, hs, hprecision⟩ :=
    RunSpec.endpoint_state R.run R.positive_degree
  exact ⟨(R.terminal s hs hprecision).toSymbolApproximation⟩

theorem assemble_from_step (R : AssembledApproximation g A T) :
    Nonempty (SymbolApproximation K g A T) := endpoint R

end AssembledApproximation

end MakarLimanov.FiniteNewtonApproximation
