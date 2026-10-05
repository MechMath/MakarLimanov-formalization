import MakarLimanov.ControlledMatrix
import MakarLimanov.BoundaryRank
import Mathlib.Algebra.FreeAlgebra

/-!
# Polynomial compression with common boundary support

Finite-word evaluation is compared entrywise with evaluation in the controlled infinite
matrix ring. The same input and output boundary strips work for every word of bounded length.
-/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.ControlledMatrix

variable {K : Type*} {P : ℤ × ℤ → Prop}

section Words

variable [Ring K]

/-- A word of length n in matrices of bound R has bound nR. -/
theorem list_prod_bound (L : List (Controlled P K)) {R : ℤ}
    (hL : ∀ A ∈ L, HasBound A.entries R) :
    HasBound L.prod.entries ((L.length : ℤ) * R) := by
  induction L with
  | nil =>
    simp only [List.prod_nil, List.length_nil, Nat.cast_zero, zero_mul]
    change HasBound (scalarMatrix (P := P) (1 : K)) 0
    exact scalar_bound (P := P) (1 : K)
  | cons A L ih =>
    have hA := hL A (by simp)
    have htail := ih (fun B hB ↦ hL B (by simp [hB]))
    have hp := product_bound A.entries L.prod.entries hA htail
    change HasBound (product A.entries L.prod.entries) _
    simpa only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul, add_comm] using hp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Word compression agrees away from common endpoint strips, with no path assumptions. -/
theorem list_prod_compress_entry (e : ι ↪ Index P) {N R : ℤ} (hR : 0 ≤ R)
    (hsquare : ∀ k : Index P,
      k ∈ Set.range e ↔ 0 ≤ k.val.1 ∧ k.val.1 < N ∧ 0 ≤ k.val.2 ∧ k.val.2 < N)
    (L : List (Controlled P K)) (hL : ∀ A ∈ L, HasBound A.entries R)
    (i j : ι)
    (hin : (e j).val.1 < N - (L.length : ℤ) * R ∧
      (L.length : ℤ) * R ≤ (e j).val.2)
    (hout : (L.length : ℤ) * R ≤ (e i).val.1 ∧
      (e i).val.2 < N - (L.length : ℤ) * R) :
    compress e L.prod.entries i j = (L.map (fun A ↦ compress e A.entries)).prod i j := by
  induction L generalizing i j with
  | nil =>
    change scalarMatrix 1 (e i) (e j) = (1 : Matrix ι ι K) i j
    simp [scalarMatrix, Matrix.one_apply, e.injective.eq_iff]
  | cons A L ih =>
    have hA := hL A (by simp)
    have htail : ∀ B ∈ L, HasBound B.entries R := fun B hB ↦ hL B (by simp [hB])
    have hprod := list_prod_bound L htail
    have hlen : ((A :: L).length : ℤ) * R = (L.length : ℤ) * R + R := by
      simp [List.length_cons, add_mul]
    rw [hlen] at hin hout
    have hclosed : ∀ k, A.entries (e i) k ≠ 0 → L.prod.entries k (e j) ≠ 0 →
        k ∈ Set.range e := by
      intro k hkA hkL
      obtain ⟨ha, hc⟩ := hA _ _ hkA
      obtain ⟨hb, hd⟩ := hprod _ _ hkL
      apply (hsquare k).2
      have hm : 0 ≤ (L.length : ℤ) * R := mul_nonneg (by omega) hR
      omega
    have hcomp := compress_product_entry e A.entries L.prod.entries i j hclosed
    change compress e (product A.entries L.prod.entries) i j =
      (compress e A.entries * (L.map (fun B ↦ compress e B.entries)).prod) i j
    rw [hcomp, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : A.entries (e i) (e k) = 0
    · simp [compress, hk]
    · have hki := hA _ _ hk
      have heq := ih htail k j (by omega) (by omega)
      rw [heq]

end Words

section Polynomials

variable [CommRing K] {σ ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The canonical coefficient representation of a free polynomial as a finite word sum. -/
noncomputable def wordCoefficients (f : FreeAlgebra K σ) : MonoidAlgebra K (FreeMonoid σ) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid f

/-- Evaluation is the finite sum of coefficients times ordered products of letters. -/
theorem lift_eq_word_sum {A : Type*} [Ring A] [Algebra K A]
    (f : FreeAlgebra K σ) (X : σ → A) :
    FreeAlgebra.lift K X f = (wordCoefficients f).coeff.sum
      (fun w c ↦ c • (w.toList.map X).prod) := by
  have hh : FreeAlgebra.lift K X =
      (MonoidAlgebra.lift K A (FreeMonoid σ) (FreeMonoid.lift X)).comp
        FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hh]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, wordCoefficients,
    MonoidAlgebra.lift_apply, FreeMonoid.lift_apply]

/-- Compression is linear, though it need not preserve multiplication. -/
noncomputable def compressLinear (e : ι ↪ Index P) :
    Controlled P K →ₗ[K] Matrix ι ι K where
  toFun A := compress e A.entries
  map_add' A B := rfl
  map_smul' c A := by
    ext i j
    change (c • A) (e i) (e j) = c * A (e i) (e j)
    rw [Algebra.smul_def]
    change product (scalarMatrix c) A.entries (e i) (e j) = _
    rw [scalar_product]

/-- Every word occurring in f has the specified length bound. -/
def DegreeBound (f : FreeAlgebra K σ) (D : ℕ) : Prop :=
  ∀ w ∈ (wordCoefficients f).coeff.support, w.toList.length ≤ D

/-- Maximum word length in the canonical support, with zero assigned degree zero. -/
noncomputable def wordDegree (f : FreeAlgebra K σ) : ℕ :=
  (wordCoefficients f).coeff.support.sup (fun w ↦ w.toList.length)

theorem degreeBound_wordDegree (f : FreeAlgebra K σ) : DegreeBound f (wordDegree f) := by
  intro w hw
  exact Finset.le_sup hw

/-- Away from common endpoint strips, compression commutes with free-polynomial evaluation. -/
theorem polynomial_compress_entry (e : ι ↪ Index P) {N R : ℤ} (hR : 0 ≤ R)
    (hsquare : ∀ k : Index P,
      k ∈ Set.range e ↔ 0 ≤ k.val.1 ∧ k.val.1 < N ∧ 0 ≤ k.val.2 ∧ k.val.2 < N)
    (f : FreeAlgebra K σ) {D : ℕ} (hD : DegreeBound f D)
    (X : σ → Controlled P K) (hX : ∀ s, HasBound (X s).entries R)
    (i j : ι)
    (hin : (e j).val.1 < N - (D : ℤ) * R ∧ (D : ℤ) * R ≤ (e j).val.2)
    (hout : (D : ℤ) * R ≤ (e i).val.1 ∧ (e i).val.2 < N - (D : ℤ) * R) :
    compress e (FreeAlgebra.lift K X f).entries i j =
      FreeAlgebra.lift K (fun s ↦ compress e (X s).entries) f i j := by
  change compressLinear e (FreeAlgebra.lift K X f) i j = _
  rw [lift_eq_word_sum, lift_eq_word_sum]
  simp only [Finsupp.sum, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro w hw
  have hlen : ((w.toList.map X).length : ℤ) * R ≤ (D : ℤ) * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    simp only [List.length_map]
    exact_mod_cast hD w hw
  have heq := list_prod_compress_entry e hR hsquare (w.toList.map X)
    (by intro A hA; obtain ⟨s, _, rfl⟩ := List.mem_map.mp hA; exact hX s)
    i j (by omega) (by omega)
  change (wordCoefficients f).coeff w * compress e (w.toList.map X).prod.entries i j = _
  rw [heq]
  simp only [List.map_map, Function.comp_def, smul_eq_mul]

end Polynomials

section Rank

variable [Field K] {σ ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The common output boundary consists of the left and upper coordinate strips. -/
def outputBoundary (e : ι ↪ Index P) (N B : ℤ) : Finset ι :=
  Finset.univ.filter fun i ↦ (e i).val.1 < B ∨ N - B ≤ (e i).val.2

/-- The common input boundary consists of the right and lower coordinate strips. -/
def inputBoundary (e : ι ↪ Index P) (N B : ℤ) : Finset ι :=
  Finset.univ.filter fun j ↦ N - B ≤ (e j).val.1 ∨ (e j).val.2 < B

/-- A negative-order infinite residual gives the common-boundary rank bound after compression. -/
theorem polynomial_compress_rank_le (e : ι ↪ Index P) {N R T : ℤ}
    (hR : 0 ≤ R) (hNT : N ≤ T)
    (hsquare : ∀ k : Index P,
      k ∈ Set.range e ↔ 0 ≤ k.val.1 ∧ k.val.1 < N ∧ 0 ≤ k.val.2 ∧ k.val.2 < N)
    (f : FreeAlgebra K σ) {D : ℕ} (hD : DegreeBound f D)
    (X : σ → Controlled P K) (hX : ∀ s, HasBound (X s).entries R)
    (hres : HasBound (FreeAlgebra.lift K X f).entries (-T)) :
    (FreeAlgebra.lift K (fun s ↦ compress e (X s).entries) f).rank ≤
      (outputBoundary e N ((D : ℤ) * R)).card +
      (inputBoundary e N ((D : ℤ) * R)).card := by
  have hzero := compress_zero_of_negative_bound e _ hres hNT (fun i ↦ by
    have hi := (hsquare (e i)).1 ⟨i, rfl⟩
    exact ⟨hi.1, hi.2.1⟩)
  apply MakarLimanov.rank_le_boundary
  intro i j hi hj
  have hout : (D : ℤ) * R ≤ (e i).val.1 ∧ (e i).val.2 < N - (D : ℤ) * R := by
    simp only [outputBoundary, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
    omega
  have hin : (e j).val.1 < N - (D : ℤ) * R ∧ (D : ℤ) * R ≤ (e j).val.2 := by
    simp only [inputBoundary, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hj
    omega
  rw [← polynomial_compress_entry e hR hsquare f hD X hX i j hin hout, hzero]
  rfl

end Rank

section Counting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Fiber cardinal bounds sum over a finite coordinate range. -/
theorem card_filter_mem_le (v : ι → ℤ) (t : Finset ℤ) (S : ℕ)
    (hf : ∀ a, (Finset.univ.filter fun i ↦ v i = a).card ≤ S) :
    (Finset.univ.filter fun i ↦ v i ∈ t).card ≤ t.card * S := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    ∑ a ∈ t, (Finset.univ.filter fun i ↦ v i = a).card ≤ ∑ _a ∈ t, S :=
      Finset.sum_le_sum fun a _ ↦ hf a
    _ = t.card * S := by simp

omit [DecidableEq ι] in
/-- A lower strip of B integer coordinates has at most B*S indices. -/
theorem card_lower_strip_le (v : ι → ℤ) (B S : ℕ) (hv : ∀ i, 0 ≤ v i)
    (hf : ∀ a, (Finset.univ.filter fun i ↦ v i = a).card ≤ S) :
    (Finset.univ.filter fun i ↦ v i < (B : ℤ)).card ≤ B * S := by
  have heq : (Finset.univ.filter fun i ↦ v i < (B : ℤ)) =
      Finset.univ.filter (fun i ↦ v i ∈ Finset.Ico 0 (B : ℤ)) := by
    ext i
    simp [hv i]
  rw [heq]
  simpa [Int.card_Ico] using card_filter_mem_le v (Finset.Ico 0 (B : ℤ)) S hf

omit [DecidableEq ι] in
/-- An upper strip of B integer coordinates has at most B*S indices. -/
theorem card_upper_strip_le (v : ι → ℤ) (N : ℤ) (B S : ℕ) (hv : ∀ i, v i < N)
    (hf : ∀ a, (Finset.univ.filter fun i ↦ v i = a).card ≤ S) :
    (Finset.univ.filter fun i ↦ N - (B : ℤ) ≤ v i).card ≤ B * S := by
  have heq : (Finset.univ.filter fun i ↦ N - (B : ℤ) ≤ v i) =
      Finset.univ.filter (fun i ↦ v i ∈ Finset.Ico (N - (B : ℤ)) N) := by
    ext i
    simp [hv i]
  rw [heq]
  simpa [Int.card_Ico] using card_filter_mem_le v (Finset.Ico (N - (B : ℤ)) N) S hf

/-- Both common boundaries together occupy at most four strips. -/
theorem boundary_card_le (e : ι ↪ Index P) (N : ℤ) (B S : ℕ)
    (hsquare : ∀ i, 0 ≤ (e i).val.1 ∧ (e i).val.1 < N ∧
      0 ≤ (e i).val.2 ∧ (e i).val.2 < N)
    (hf₁ : ∀ a, (Finset.univ.filter fun i ↦ (e i).val.1 = a).card ≤ S)
    (hf₂ : ∀ c, (Finset.univ.filter fun i ↦ (e i).val.2 = c).card ≤ S) :
    (outputBoundary e N (B : ℤ)).card + (inputBoundary e N (B : ℤ)).card ≤ 4 * B * S := by
  have hl₁ := card_lower_strip_le (fun i ↦ (e i).val.1) B S (fun i ↦ (hsquare i).1) hf₁
  have hu₁ := card_upper_strip_le (fun i ↦ (e i).val.1) N B S
    (fun i ↦ (hsquare i).2.1) hf₁
  have hl₂ := card_lower_strip_le (fun i ↦ (e i).val.2) B S
    (fun i ↦ (hsquare i).2.2.1) hf₂
  have hu₂ := card_upper_strip_le (fun i ↦ (e i).val.2) N B S
    (fun i ↦ (hsquare i).2.2.2) hf₂
  simp only [outputBoundary, inputBoundary, Finset.filter_or]
  have ho := Finset.card_union_le
    (Finset.univ.filter fun i ↦ (e i).val.1 < (B : ℤ))
    (Finset.univ.filter fun i ↦ N - (B : ℤ) ≤ (e i).val.2)
  have hi := Finset.card_union_le
    (Finset.univ.filter fun i ↦ N - (B : ℤ) ≤ (e i).val.1)
    (Finset.univ.filter fun i ↦ (e i).val.2 < (B : ℤ))
  nlinarith

end Counting

/-- Quantitative polynomial compression once the square's coordinate fibers are bounded. -/
theorem polynomial_compress_rank_le_four [Field K] {σ ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι ↪ Index P) {N T : ℤ} {R S D : ℕ}
    (hNT : N ≤ T)
    (hsquare : ∀ k : Index P,
      k ∈ Set.range e ↔ 0 ≤ k.val.1 ∧ k.val.1 < N ∧ 0 ≤ k.val.2 ∧ k.val.2 < N)
    (hf₁ : ∀ a, (Finset.univ.filter fun i ↦ (e i).val.1 = a).card ≤ S)
    (hf₂ : ∀ c, (Finset.univ.filter fun i ↦ (e i).val.2 = c).card ≤ S)
    (f : FreeAlgebra K σ) (hD : DegreeBound f D)
    (X : σ → Controlled P K) (hX : ∀ s, HasBound (X s).entries (R : ℤ))
    (hres : HasBound (FreeAlgebra.lift K X f).entries (-T)) :
    (FreeAlgebra.lift K (fun s ↦ compress e (X s).entries) f).rank ≤ 4 * D * R * S := by
  have hrank := polynomial_compress_rank_le e (by positivity : (0 : ℤ) ≤ R)
    hNT hsquare f hD X hX hres
  have hcard := boundary_card_le e N (D * R) S
    (fun i ↦ (hsquare (e i)).1 ⟨i, rfl⟩) hf₁ hf₂
  simp only [Nat.cast_mul] at hcard
  exact hrank.trans (by simpa only [Nat.mul_assoc] using hcard)

end MakarLimanov.ControlledMatrix
