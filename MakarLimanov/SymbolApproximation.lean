import MakarLimanov.SymbolSeries
import MakarLimanov.BinarySupport

/-!
# Finite symbol approximation data

This module contains only the data type used by the finite Newton proposition.
Keeping it separate from the theorem interfaces lets the Newton construction
refer to its output type without a circular import.
-/

noncomputable section

namespace MakarLimanov.AuditedAssumptions

open SymbolSeries ControlledMatrix

universe u

structure SymbolApproximation (K : Type u) [Field K]
    (g : FreeAlgebra K Bool) (A T : ℕ) where
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
    (StarSeries.toSeries
      (StarSeries.evaluateAt (hp := hp) (h := commute) Z (1 + g)))

attribute [instance] SymbolApproximation.field SymbolApproximation.algebra
  SymbolApproximation.charZero

end MakarLimanov.AuditedAssumptions
