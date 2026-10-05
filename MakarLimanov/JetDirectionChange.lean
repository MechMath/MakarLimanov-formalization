import MakarLimanov.JetTransform
import MakarLimanov.NewtonCKRoot
import MakarLimanov.JetLeaderDirection

/-! The change of differential directions in equation (4.2) of `proof.tex`.
Unlike the eigenvector twist, this substitution preserves total differential order.
-/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.JetDirectionChange

open MvPolynomial NewtonCKRoot JetTransform

noncomputable section

variable {F : Type*} [Field F] {N : ℕ}

/-- The jets on a fixed diagonal, extended by zero outside that diagonal. -/
def diagonal (n : ℕ) (hn : n ≤ N) (b : ℕ) : MvPolynomial (Triangle N) F :=
  if hb : b ≤ n then X ⟨(n - b, b), by omega⟩ else 0

theorem transform_congr_upto {R : Type*} [CommRing R] (s : R) (a b : ℕ → R)
    (n : ℕ) (hab : ∀ j ≤ n, a j = b j) : transform s a n = transform s b n := by
  induction n generalizing a b with
  | zero => exact hab 0 le_rfl
  | succ n ih =>
    rw [transform, transform, ih a b (fun j hj ↦ hab j (by omega)),
      ih (fun j ↦ a (j + 1)) (fun j ↦ b (j + 1)) (fun j hj ↦ hab (j + 1) (by omega))]

/-- Replace the second differential direction by the second plus `c` times the first. -/
def change (c : F) : MvPolynomial (Triangle N) F →ₐ[F] MvPolynomial (Triangle N) F :=
  aeval (fun ij ↦ transform (C c) (diagonal (ij.val.1 + ij.val.2) ij.property) ij.val.2)

@[simp] theorem change_C (c a : F) : change (N := N) c (C a) = C a := by
  simp [change]

@[simp] theorem change_X (c : F) (ij : Triangle N) :
    change c (X ij) = transform (C c) (diagonal (ij.val.1 + ij.val.2) ij.property)
      ij.val.2 := by
  simp [change]

theorem change_diagonal (c : F) (n : ℕ) (hn : n ≤ N) (b : ℕ) (hb : b ≤ n) :
    change c (diagonal n hn b) = transform (C c) (diagonal n hn) b := by
  rw [diagonal, dif_pos hb, change_X]
  dsimp only
  congr 2
  omega

/-- The two finite triangular substitutions compose by addition of their parameters. -/
theorem change_comp (c d : F) :
    (change (N := N) c).comp (change d) = change (c + d) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, change_X]
  have hm := map_transform (change (N := N) c).toRingHom (C d)
    (diagonal (ij.val.1 + ij.val.2) ij.property) ij.val.2
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, change_C] at hm
  rw [hm]
  have heq := transform_congr_upto (C d)
    (fun b ↦ change c (diagonal (ij.val.1 + ij.val.2) ij.property b))
    (transform (C c) (diagonal (ij.val.1 + ij.val.2) ij.property)) ij.val.2
    (fun b hb ↦ change_diagonal c _ _ b (by omega))
  rw [heq, transform_comp, ← map_add, add_comm d c]

@[simp] theorem change_zero : change (N := N) (0 : F) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro ij
  rw [change_X, map_zero, transform_zero, diagonal, dif_pos (by omega)]
  simp

/-- The inverse direction change uses `-c`. -/
def changeEquiv (c : F) :
    MvPolynomial (Triangle N) F ≃ₐ[F] MvPolynomial (Triangle N) F :=
  AlgEquiv.ofAlgHom (change c) (change (-c))
    (by rw [change_comp, add_neg_cancel, change_zero])
    (by rw [change_comp, neg_add_cancel, change_zero])

theorem change_injective (c : F) : Function.Injective (change (N := N) c) :=
  (changeEquiv c).injective

theorem pderiv_transform (c : F) (a : ℕ → MvPolynomial (Triangle N) F)
    (n : ℕ) (q : Triangle N) :
    pderiv q (transform (C c) a n) = transform (C c) (fun j ↦ pderiv q (a j)) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [transform, map_add, pderiv_C_mul, ih]

theorem pderiv_leader_diagonal (n : ℕ) (hn : n ≤ N) (b : ℕ) :
    pderiv (leader N) (diagonal (F := F) n hn b) =
      if n = N ∧ b = 0 then 1 else 0 := by
  classical
  unfold diagonal
  split_ifs with hb hab
  · obtain ⟨rfl, rfl⟩ := hab
    simp [leader]
  · have hne : (⟨(n - b, b), by omega⟩ : Triangle N) ≠ leader N := by
      intro heq
      have hpair := congrArg Subtype.val heq
      dsimp [leader] at hpair
      have := congrArg Prod.fst hpair
      have := congrArg Prod.snd hpair
      apply hab
      constructor <;> omega
    exact pderiv_X_of_ne hne
  · omega
  · simp

theorem transform_delta {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    transform c (fun j ↦ if j = 0 then 1 else 0) n = c ^ n := by
  rw [transform_eq_sum]
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · intro ab hab hne
    have ha : ab.1 ≠ 0 := by
      intro ha
      have hb := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      apply hne
      exact Prod.ext ha (by omega)
    simp [ha]
  · simp

/-- The pure highest derivative of a transformed generator records its top diagonal weight. -/
theorem pderiv_leader_change_X (c : F) (ij : Triangle N) :
    pderiv (leader N) (change c (X ij)) =
      if ij.val.1 + ij.val.2 = N then C (c ^ ij.val.2) else 0 := by
  rw [change_X, pderiv_transform]
  simp_rw [pderiv_leader_diagonal]
  by_cases hn : ij.val.1 + ij.val.2 = N
  · simp only [hn, true_and, ↓reduceIte]
    have hd := transform_delta (C (σ := Triangle N) c) ij.val.2
    simpa using hd
  · simp only [hn, false_and, ↓reduceIte]
    rw [transform_eq_sum]
    simp

set_option maxHeartbeats 800000 in
/-- Chain rule for the pure highest derivative, expressed on the original jet coordinates. -/
theorem pderiv_leader_change (c : F) (P : MvPolynomial (Triangle N) F) :
    pderiv (leader N) (change c P) = change c
      (∑ j : Fin (N + 1), C c ^ j.val * pderiv (JetLeaderDirection.topJet N j) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, mul_add, Finset.sum_add_distrib]
  | mul_X P ij hP =>
    simp only [map_mul, pderiv_mul, hP, Finset.sum_mul,
      mul_add, Finset.sum_add_distrib, map_add, map_sum]
    congr 1
    · simp only [mul_assoc]
    · rw [pderiv_leader_change_X]
      by_cases hn : ij.val.1 + ij.val.2 = N
      · let j : Fin (N + 1) := ⟨ij.val.2, by have := ij.property; omega⟩
        have hij : JetLeaderDirection.topJet N j = ij := by
          apply Subtype.ext
          dsimp [JetLeaderDirection.topJet, j]
          apply Prod.ext <;> omega
        have heq (l : Fin (N + 1)) : ij = JetLeaderDirection.topJet N l ↔ l = j := by
          constructor
          · intro h
            apply Fin.ext
            have := congrArg (fun q : Triangle N ↦ q.val.2) h
            simpa [JetLeaderDirection.topJet, j] using this.symm
          · rintro rfl
            exact hij.symm
        simp [pderiv_X, Pi.single_apply, heq, hn, j, mul_comm]
      · have hne (l : Fin (N + 1)) : ij ≠ JetLeaderDirection.topJet N l := by
          intro h
          apply hn
          rw [h]
          dsimp [JetLeaderDirection.topJet]
          omega
        simp [pderiv_X, hne, hn]

/-- A base-field change of directions gives a nonzero pure highest partial derivative. -/
theorem exists_change_pderiv_leader_ne_zero {k : Type*} [Field k] [Infinite k]
    [Algebra k F] [CharZero F] (P : MvPolynomial (Triangle N) F)
    (horder : FiniteJets.differentialOrder (FiniteJets.includeTriangle N P) = N)
    (hN : 0 < N) :
    ∃ c : k, pderiv (leader N) (change (algebraMap k F c) P) ≠ 0 := by
  obtain ⟨c, hc⟩ := JetLeaderDirection.exists_top_direction_of_order (k := k) P horder hN
  refine ⟨c, ?_⟩
  rw [pderiv_leader_change]
  exact (map_ne_zero_iff (change (algebraMap k F c)) (change_injective _)).mpr hc

end
end MakarLimanov.JetDirectionChange
