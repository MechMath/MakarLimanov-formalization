import MakarLimanov.GenericResidualBounds
import MakarLimanov.GenericSlopeRefinement
import MakarLimanov.ExactGenericSlope
import MakarLimanov.RationalSlopeRefinement

/-!
# Moving the next supporting line onto an integral lattice

The supporting-line inequalities are stated at a rational slope in the
current exponent coordinate.  Refining by the denominator factor turns that
slope into an integer correction exponent and transports every variation
bound to the refined lattice.
-/

noncomputable section

namespace MakarLimanov.NextSlopeRefinedResidual

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients NewtonResidual

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

private theorem genericVariation_zero_eq_mapField_evaluateAt
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) :
    genericVariation (E := E) δ η hc p hp q z f 0 =
      mapField (IsScalarTower.toAlgHom k F E)
        (toSeries (evaluateAt (hp := hp) (h := hc) z f)) := by
  have hzero : genericVariation (E := E) δ η hc p hp q z f 0 =
      toSeries (evaluateAt (hp := hp)
        (h := GenericJets.commute δ η hc)
        (mapField (IsScalarTower.toAlgHom k F E) z) f) := by
    simp [genericVariation, SymbolVariations.variation,
      Variations.variation_zero, evaluateAt, evaluatePair, evaluate, apply_ite]
  rw [hzero]
  symm
  exact SymbolSeries.mapField_evaluateAt
    (IsScalarTower.toAlgHom k F E) p hp δ η
    (GenericJets.delta δ) (GenericJets.eta η) hc (GenericJets.commute δ η hc)
    (fun a ↦ (GenericJets.delta_base δ a).symm)
    (fun a ↦ (GenericJets.eta_base η a).symm) z f

/-- The support-line inequalities at `s` become a lower bound for the full
generic residual after refining the denominator.  Here `q' = e*s` is the
integer exponent on the refined lattice. -/
theorem lowerBound_after_refined_slope
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (rho : ℤ) (s : ℚ)
    (active : Finset ℕ)
    (hactive : ∀ i, i ∈ active ↔
      i ≤ ControlledMatrix.wordDegree f ∧ 0 < i ∧
        genericVariation (E := E) δ η hc p hp 0 z f i ≠ 0)
    (hline : ∀ i ∈ active,
      (rho : ℚ) ≤
        ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
          (i : ℚ) * (s - (q : ℚ)))
    (hrho : rho =
      (toSeries (evaluateAt (hp := hp) (h := hc) z f)).order)
    (e : ℕ) (he : 0 < e) (q' : ℤ)
    (hq' : (q' : ℚ) = (e : ℚ) * s) :
    LowerBound ((e : ℤ) * rho)
      (genericResidual (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        q' (refineLattice e he z) f) := by
  apply (GenericResidualBounds.genericResidual_lowerBound_iff
    (E := E) δ η hc (p * e) (Nat.mul_pos hp he) q'
    (refineLattice e he z) f ((e : ℤ) * rho)).2
  intro i
  by_cases hi0 : i = 0
  · subst i
    have hvar0 := genericVariation_zero_eq_mapField_evaluateAt
      (E := E) δ η hc (p * e) (Nat.mul_pos hp he) q'
      (refineLattice e he z) f
    have htransport := SymbolSeries.refineLattice_evaluateAt
      p e hp he δ η hc z f
    rw [hvar0, ← htransport]
    apply (lowerBound_mapField_iff (IsScalarTower.toAlgHom k F E)
      ((e : ℤ) * rho) _).mpr
    apply (lowerBound_refineLattice_iff e he rho _).mpr
    rw [hrho]
    exact lowerBound_order _
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    by_cases hv0 : genericVariation (E := E) δ η hc p hp 0 z f i ≠ 0
    · have hideg : i ≤ ControlledMatrix.wordDegree f := by
        by_contra hnot
        exact hv0 (GenericResidualHomogeneous.genericResidual_variation_degree_bound
          (E := E) δ η hc p hp 0 z f i (Nat.lt_of_not_ge hnot))
      have hbound := hline i ((hactive i).mpr ⟨hideg, hipos, hv0⟩)
      have hslope := ExactGenericSlope.genericVariation_slope
        (E := E) δ η hc p hp q z f i
      have hbaseQ :
          ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) =
            (i : ℚ) * (q : ℚ) +
              ((genericVariation (E := E) δ η hc p hp 0 z f i).order : ℚ) := by
        rw [hslope.2 hv0]
        push_cast
        rfl
      rw [hbaseQ] at hbound
      have hbase : (rho : ℚ) ≤
          ((genericVariation (E := E) δ η hc p hp 0 z f i).order : ℚ) +
            (i : ℚ) * s := by
        nlinarith [hbound]
      have href0 := GenericSlopeRefinement.refineLattice_genericVariation_zero_order
        (E := E) δ η hc p e hp he z f i hv0
      have hnew0 :
          genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
            0 (refineLattice e he z) f i ≠ 0 := by
        intro hz
        apply hv0
        exact (GenericSlopeRefinement.refineLattice_genericVariation_eq_zero_iff
          (E := E) δ η hc p e hp he 0 z f i).mpr (by simpa using hz)
      have hslope' := ExactGenericSlope.genericVariation_slope
        (E := E) δ η hc (p * e) (Nat.mul_pos hp he) q'
        (refineLattice e he z) f i
      have hnew :
          genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
            q' (refineLattice e he z) f i ≠ 0 := by
        intro hz
        exact hnew0 (hslope'.1.mp hz)
      have hnewOrderQ :
          ((genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
            q' (refineLattice e he z) f i).order : ℚ) =
              (i : ℚ) * (q' : ℚ) +
                (e : ℚ) *
                  ((genericVariation (E := E) δ η hc p hp 0 z f i).order : ℚ) := by
        rw [hslope'.2 hnew0, href0]
        push_cast
        rfl
      have hmul := mul_le_mul_of_nonneg_left hbase
        (show (0 : ℚ) ≤ (e : ℚ) by positivity)
      have hfinal : (e : ℚ) * (rho : ℚ) ≤
          ((genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
            q' (refineLattice e he z) f i).order : ℚ) := by
        rw [hnewOrderQ, hq']
        nlinarith [hmul]
      exact (HahnSeries.le_order_iff_forall hnew).mp (by exact_mod_cast hfinal)
    · have hv0 : genericVariation (E := E) δ η hc p hp 0 z f i = 0 := not_ne_iff.mp hv0
      have hvref0 :
          genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
            0 (refineLattice e he z) f i = 0 := by
        simpa using (GenericSlopeRefinement.refineLattice_genericVariation_eq_zero_iff
          (E := E) δ η hc p e hp he 0 z f i).mp hv0
      have hslope' := ExactGenericSlope.genericVariation_slope
        (E := E) δ η hc (p * e) (Nat.mul_pos hp he) q'
        (refineLattice e he z) f i
      have hvnew := hslope'.1.mpr hvref0
      rw [hvnew]
      intro n hn
      exact coeff_zero

/-- The factor selected by the paper's least common multiple rule makes the
next rational supporting slope an integer exponent on the refined lattice. -/
theorem exists_refined_slope_exponent (p : ℕ) (hp : 0 < p) (s : ℚ) :
    ∃ e : ℕ, ∃ q' : ℤ,
      e = RationalSlopeRefinement.refinementFactor p (s / p) ∧ 0 < e ∧
      (q' : ℚ) = (e : ℚ) * s ∧
      (q' : ℚ) / (p * e : ℕ) = s / p := by
  obtain ⟨e, q', hfactor, he, hq', hdiv⟩ :=
    RationalSlopeRefinement.exists_refinement_data p hp (s / p)
  refine ⟨e, q', hfactor, he, ?_, hdiv⟩
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq'' : (q' : ℚ) = (p * e : ℕ) * (s / p) := hq'
  rw [hq'']
  field_simp [hpQ]
  push_cast
  ring

end MakarLimanov.NextSlopeRefinedResidual

end
