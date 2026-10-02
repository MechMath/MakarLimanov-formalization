import MakarLimanov.SymbolTransport

/-!
# Order-form bounds used by the Newton proposition

The paper states its symbol estimates using the least Laurent index (the
negative of the displayed differential-operator order).  The audited API uses
`LowerBound`; these two small lemmas are the exact conversion needed when an
order-form Newton construction is assembled.
-/

namespace MakarLimanov.NewtonOrderBridge

open SymbolSeries

variable {F : Type*} [Field F]

/-- A lower bound on the least occupied Laurent index gives the corresponding
`LowerBound` predicate. -/
theorem lowerBound_of_order_ge (x : LaurentSeries F) (b : ℤ)
    (h : b ≤ x.order) : LowerBound b x :=
  (lowerBound_order x).mono h

/-- The zero series satisfies every lower support bound. -/
theorem lowerBound_zero (b : ℤ) : LowerBound b (0 : LaurentSeries F) := by
  intro n hn
  exact HahnSeries.coeff_zero

/-- If an order-form construction either reaches the required order or has
already produced the zero residual, it supplies the lower-bound formulation. -/
theorem lowerBound_of_order_or_zero (x : LaurentSeries F) (b : ℤ)
    (hx : x = 0 ∨ b ≤ x.order) : LowerBound b x := by
  rcases hx with rfl | h
  · exact lowerBound_zero b
  · exact lowerBound_of_order_ge x b h

end MakarLimanov.NewtonOrderBridge

