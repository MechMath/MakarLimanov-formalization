import MakarLimanov.DifferentialSeparation
import MakarLimanov.SymbolVariations
import MakarLimanov.Compression

/-!
# A checked lower-bound bridge for star evaluations

This file records the support estimate that is needed before comparing the
concrete differential-operator model with the star-symbol model.  It is proved
directly from the finite word expansion and the star-product lower-bound
lemma; no realization or separation assumption is used.
-/

namespace MakarLimanov.OperatorStarBridge

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open MakarLimanov.ControlledMatrix

noncomputable section

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [CharZero F]

private theorem lowerBound_zero (b : ℤ) : LowerBound b (0 : LaurentSeries F) := by
  intro n hn
  exact HahnSeries.coeff_zero

private theorem lowerBound_one : LowerBound 0 (1 : LaurentSeries F) := by
  intro n hn
  simp [HahnSeries.coeff_one, hn.ne]

private theorem lowerBound_add_of_le {b c : ℤ} {x y : LaurentSeries F}
    (hx : LowerBound b x) (hy : LowerBound c y) (hbc : b ≤ c) :
    LowerBound b (x + y) := by
  intro n hn
  rw [coeff_add]
  simp [hx n hn, hy n (hn.trans_le hbc)]

private theorem lowerBound_list_prod
    {p : ℕ} (hp : 0 < p) (δ η : Derivation k F F)
    (h : Function.Commute δ η)
    (X : Bool → StarSeries p hp δ η h) (b : ℤ)
    (hb : ∀ c : Bool, LowerBound b (toSeries (X c))) :
    ∀ w : List Bool, LowerBound ((w.length : ℤ) * b)
      (toSeries ((w.map X).prod)) := by
  intro w
  induction w with
  | nil =>
      simpa using lowerBound_one (F := F)
  | cons c w ih =>
      simp only [List.map_cons, List.prod_cons, toSeries_mul]
      have hw := ih
      have hc := hb c
      have hmul := hc.starProduct hw p hp δ η
      convert hmul using 1 <;> push_cast <;> simp [Nat.cast_add, add_mul, add_comm]

private theorem lowerBound_word_sum
    {p : ℕ} (hp : 0 < p) (δ η : Derivation k F F)
    (h : Function.Commute δ η)
    (X : Bool → StarSeries p hp δ η h) (b : ℤ)
    (hb : ∀ c : Bool, LowerBound b (toSeries (X c)))
    (f : FreeAlgebra k Bool) (M : ℕ)
    (hbneg : b ≤ 0)
    (hM : ∀ w ∈ (wordCoefficients f).support, w.toList.length ≤ M) :
    LowerBound ((M : ℤ) * b)
      (toSeries (FreeAlgebra.lift k X f)) := by
  rw [ControlledMatrix.lift_eq_word_sum]
  let s := wordCoefficients f
  have hs : ∀ s : FreeMonoid Bool →₀ k,
      s.support ⊆ (wordCoefficients f).support →
      LowerBound ((M : ℤ) * b)
        (toSeries (s.sum (fun w c ↦ c • (w.toList.map X).prod))) := by
    classical
    intro s
    induction s using Finsupp.induction with
    | zero =>
        intro _
        simpa using lowerBound_zero (F := F) ((M : ℤ) * b)
    | @single_add w c s hws hc ih =>
        intro hsub
        rw [Finsupp.sum_add_index]
        · rw [Finsupp.sum_single_index]
          · apply LowerBound.add
            · have hwadd : w ∈ (Finsupp.single w c + s).support := by
                rw [Finsupp.mem_support_iff]
                have hsw : s w = 0 := by
                  by_contra hne
                  exact hws (Finsupp.mem_support_iff.mpr hne)
                simp [Finsupp.single_eq_same, hsw, hc]
              have hwf : w ∈ (wordCoefficients f).support := hsub hwadd
              have hlen := hM w hwf
              have hwprod := lowerBound_list_prod hp δ η h X b hb (w.toList)
              have hbase : (M : ℤ) * b ≤ (w.toList.length : ℤ) * b := by
                have hlen' : (w.toList.length : ℤ) ≤ (M : ℤ) := by exact_mod_cast hlen
                nlinarith
              change LowerBound ((M : ℤ) * b)
                (toSeries (c • (w.toList.map X).prod))
              have hscalar : LowerBound 0
                  (HahnSeries.single 0 (algebraMap k F c) : LaurentSeries F) := by
                intro n hn
                exact HahnSeries.coeff_single_of_ne (by omega)
              have hscaled := hscalar.starProduct (hwprod.mono hbase) p hp δ η
              simpa [StarSeries.toSeries_smul, Algebra.smul_def] using hscaled
            · apply ih
              intro a ha
              have hadd : a ∈ (Finsupp.single w c + s).support := by
                rw [Finsupp.mem_support_iff]
                intro hz
                by_cases haw : a = w
                · subst a
                  exact False.elim (hws ha)
                · have hsa : s a ≠ 0 := Finsupp.mem_support_iff.mp ha
                  simp [Finsupp.single_apply, haw, hsa] at hz
              exact hsub hadd
          · simp
        · intro a ha
          simp
        · intro a ha x y
          simp [add_smul]
  exact hs _ (by intro w hw; exact hw)

/-- Finite word evaluation preserves the common lower bound of its letters.
The bound is multiplied by the maximal word length. -/
theorem lift_lowerBound_of_letter_bounds
    {p : ℕ} (hp : 0 < p) (δ η : Derivation k F F)
    (h : Function.Commute δ η)
    (X : Bool → StarSeries p hp δ η h) (b : ℤ)
    (hb : ∀ c : Bool, LowerBound b (toSeries (X c)))
    (f : FreeAlgebra k Bool) (M : ℕ)
    (hbneg : b ≤ 0)
    (hM : ∀ w ∈ (wordCoefficients f).support, w.toList.length ≤ M) :
    LowerBound ((M : ℤ) * b)
      (toSeries (FreeAlgebra.lift k X f)) := by
  exact lowerBound_word_sum hp δ η h X b hb f M hbneg hM

/- A direct form for the symbol evaluation used by Newton's construction. -/
theorem evaluateAt_lowerBound
    {p : ℕ} (hp : 0 < p) (δ η : Derivation k F F)
    (h : Function.Commute δ η) (z : LaurentSeries F) (b : ℤ)
    (hz : LowerBound b z) (hbneg : b ≤ -(p : ℤ))
    (f : FreeAlgebra k Bool) (M : ℕ)
    (hM : ∀ w ∈ (wordCoefficients f).support, w.toList.length ≤ M) :
    LowerBound ((M : ℤ) * b)
      (toSeries (evaluateAt (hp := hp) (h := h) z f)) := by
  let X : Bool → StarSeries p hp δ η h :=
    fun c ↦ ofSeries (if c then z else distinguishedSymbol p)
  have hX : ∀ c, LowerBound b (toSeries (X c)) := by
    intro c
    cases c
    · have hs : LowerBound b (distinguishedSymbol p : LaurentSeries F) := by
        intro n hn
        apply HahnSeries.coeff_single_of_ne
        intro heq
        have hle : n < -(p : ℤ) := hn.trans_le hbneg
        omega
      simpa [X] using hs
    · simpa [X] using hz
  have hbzero : b ≤ 0 := by
    omega
  have hmain := lift_lowerBound_of_letter_bounds hp δ η h X b hX f M hbzero hM
  simpa [X, evaluateAt, evaluatePair] using hmain

theorem evaluateAt_add_single_lowerBound
    {p : ℕ} (hp : 0 < p) (δ η : Derivation k F F)
    (h : Function.Commute δ η) (z : LaurentSeries F) (b q : ℤ)
    (hz : LowerBound b z) (hbneg : b ≤ -(p : ℤ)) (hbq : b ≤ q)
    (w : F) (f : FreeAlgebra k Bool) (M : ℕ)
    (hM : ∀ u ∈ (wordCoefficients f).support, u.toList.length ≤ M) :
    LowerBound ((M : ℤ) * b)
      (toSeries (evaluateAt (hp := hp) (h := h)
        (z + HahnSeries.single q w) f)) := by
  have hsingle : LowerBound q (HahnSeries.single q w) := by
    intro n hn
    exact HahnSeries.coeff_single_of_ne (by omega)
  have hsum : LowerBound b (z + HahnSeries.single q w) :=
    lowerBound_add_of_le hz hsingle hbq
  exact evaluateAt_lowerBound hp δ η h _ b hsum hbneg f M hM

end

end MakarLimanov.OperatorStarBridge
