import MakarLimanov.JetDirectionChange

/-!
# Changing a constant differential direction

Replacing the second derivation by `H + c • D` preserves commutation. Its mixed
jets are the binomial substitution along each fixed total-order diagonal.
-/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.DirectionDerivations

noncomputable section

variable {k F E : Type*} [CommRing k] [Field F] [Algebra k F]
  [Field E] [Algebra k E]

/-- Adding a constant multiple of the first derivation preserves commutation. -/
theorem commute_add_smul (D H : Derivation k E E) (hc : Function.Commute D H) (c : k) :
    Function.Commute D (H + c • D : Derivation k E E) := by
  intro x
  simp only [Derivation.add_apply, Derivation.smul_apply, map_add, Derivation.map_smul,
    hc x]

/-- A constant change of direction commutes with extension of the coefficient field. -/
theorem add_smul_restrict [Algebra F E] [IsScalarTower k F E]
    (δ η : Derivation k F F) (D H : Derivation k E E) (c : k)
    (hD : ∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a))
    (hH : ∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) (a : F) :
    (H + c • D : Derivation k E E) (algebraMap F E a) =
      algebraMap F E ((η + c • δ : Derivation k F F) a) := by
  simp only [Derivation.add_apply, Derivation.smul_apply, hD, hH, map_add]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply k F E]

/-- The binomial theorem for a constant linear combination of commuting derivations. -/
theorem iterate_add_smul (D H : Derivation k E E) (hc : Function.Commute D H)
    (c : k) (j : ℕ) (v : E) :
    (H + c • D : Derivation k E E)^[j] v =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        j.choose ab.1 • ((algebraMap k E c) ^ ab.2 * D^[ab.2] (H^[ab.1] v)) := by
  let d : Module.End k E := D.toLinearMap
  let h : Module.End k E := H.toLinearMap
  have hcomm : Commute h (c • d) := by
    ext x
    change H (c • D x) = c • D (H x)
    rw [Derivation.map_smul, hc x]
  change (⇑(h + c • d))^[j] v = _
  rw [← Module.End.pow_apply]
  rw [hcomm.add_pow', LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro ab hab
  simp only [LinearMap.smul_apply, Module.End.mul_apply, smul_pow,
    Module.End.pow_apply]
  change j.choose ab.1 • H^[ab.1] (c ^ ab.2 • D^[ab.2] v) = _
  have hl : H^[ab.1] (c ^ ab.2 • D^[ab.2] v) =
      c ^ ab.2 • H^[ab.1] (D^[ab.2] v) := by
    simpa only [Module.End.pow_apply, h, Derivation.coeFn_coe] using
      (h ^ ab.1).map_smul (c ^ ab.2) (D^[ab.2] v)
  rw [hl, (hc.iterate_iterate ab.2 ab.1).symm v]
  congr 1
  rw [Algebra.smul_def, map_pow]

/-- The mixed-jet formula after a constant change of the second differential direction. -/
theorem mixed_add_smul (D H : Derivation k E E) (hc : Function.Commute D H)
    (c : k) (i j : ℕ) (v : E) :
    D^[i] ((H + c • D : Derivation k E E)^[j] v) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        j.choose ab.1 • ((algebraMap k E c) ^ ab.2 * D^[i + ab.2] (H^[ab.1] v)) := by
  rw [iterate_add_smul D H hc c j v]
  change (⇑D.toLinearMap)^[i] _ = _
  rw [← Module.End.pow_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [map_nsmul, ← map_pow, ← Algebra.smul_def, LinearMap.map_smul,
    Module.End.pow_apply]
  change j.choose ab.1 • c ^ ab.2 • D^[i] (D^[ab.2] (H^[ab.1] v)) = _
  rw [← Function.iterate_add_apply]
  congr 1
  rw [Algebra.smul_def]

/-- Evaluating the finite jet direction change gives the actual changed derivations. -/
theorem aeval_change [Algebra F E] [IsScalarTower k F E] {N : ℕ}
    (D H : Derivation k E E) (hc : Function.Commute D H) (c : k) (v : E)
    (P : MvPolynomial (NewtonCKRoot.Triangle N) F) :
    MvPolynomial.aeval
        (fun ij : NewtonCKRoot.Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v))
        (JetDirectionChange.change (algebraMap k F c) P) =
      MvPolynomial.aeval
        (fun ij : NewtonCKRoot.Triangle N ↦
          D^[ij.val.1] ((H + c • D : Derivation k E E)^[ij.val.2] v)) P := by
  have hhom :
      (MvPolynomial.aeval
        (fun ij : NewtonCKRoot.Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v))).comp
          (JetDirectionChange.change (algebraMap k F c)) =
        MvPolynomial.aeval
          (fun ij : NewtonCKRoot.Triangle N ↦
            D^[ij.val.1] ((H + c • D : Derivation k E E)^[ij.val.2] v)) := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp only [AlgHom.comp_apply, JetDirectionChange.change_X,
      JetTransform.transform_eq_sum, map_sum, map_nsmul, map_mul, map_pow,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      ← IsScalarTower.algebraMap_apply k F E]
    rw [mixed_add_smul D H hc c ij.val.1 ij.val.2 v]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : ab.1 ≤ ij.val.1 + ij.val.2 := by omega
    rw [JetDirectionChange.diagonal, dif_pos ha, MvPolynomial.aeval_X]
    dsimp only
    have he : ij.val.1 + ij.val.2 - ab.1 = ij.val.1 + ab.2 := by omega
    rw [he]
  exact DFunLike.congr_fun hhom P

/-- Subtracting the same constant direction reverses the change on derivations. -/
@[simp] theorem add_neg_smul_cancel (D H : Derivation k E E) (c : k) :
    H + (-c) • D + c • D = H := by
  rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]

/-- Commutation also holds for the inverse direction change. -/
theorem commute_sub_smul (D H : Derivation k E E) (hc : Function.Commute D H) (c : k) :
    Function.Commute D (H - c • D : Derivation k E E) := by
  simpa only [neg_smul, sub_eq_add_neg] using commute_add_smul D H hc (-c)

end

end MakarLimanov.DirectionDerivations
