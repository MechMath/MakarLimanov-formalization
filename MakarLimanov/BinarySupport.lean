import MakarLimanov.TwoGenerator
import MakarLimanov.Compression

/-! Pure words cannot occur in a binary free polynomial with zero abelianization. -/

namespace MakarLimanov.BinarySupport
open ControlledMatrix
variable {K : Type*} [Field K]

noncomputable def counts (w : List Bool) : Bool →₀ ℕ :=
  (w.map (fun b ↦ Finsupp.single b 1)).sum

@[simp] lemma counts_nil : counts [] = 0 := rfl
@[simp] lemma counts_cons (b : Bool) (w : List Bool) :
    counts (b::w) = Finsupp.single b 1 + counts w := by simp [counts]

lemma counts_apply (w : List Bool) (b : Bool) : counts w b = w.count b := by
  induction w with
  | nil => simp [counts]
  | cons c w ih =>
    simp only [counts_cons, Finsupp.add_apply, ih]
    by_cases hc : c = b <;> simp [hc, Nat.add_comm]

lemma counts_replicate (b : Bool) (n : ℕ) : counts (List.replicate n b) = Finsupp.single b n := by
  ext c
  cases b <;> cases c <;> simp [counts_apply, List.count_replicate]

lemma counts_eq_single (b : Bool) (n : ℕ) (w : List Bool) :
    counts w = Finsupp.single b n ↔ w = List.replicate n b := by
  constructor
  · intro h
    have hnot : (!b) ∉ w := by
      have hh := congrArg (fun z : Bool →₀ ℕ ↦ z (!b)) h
      dsimp only at hh
      cases b <;> simpa [counts_apply, List.count_eq_zero] using hh
    have hall : ∀ c ∈ w, c = b := by
      intro c hc
      cases b <;> cases c <;> simp_all
    have hrep := List.eq_replicate_of_mem hall
    have hn := congrArg (fun z : Bool →₀ ℕ ↦ z b) h
    dsimp only at hn
    rw [hrep, counts_replicate] at hn
    simp only [Finsupp.single_eq_same] at hn
    simpa [hn] using hrep
  · rintro rfl
    exact counts_replicate b n

lemma product_X (w : List Bool) :
    (w.map (MvPolynomial.X (R := K))).prod = MvPolynomial.monomial (counts w) 1 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    simp only [List.map_cons, List.prod_cons, ih, counts_cons]
    rw [MvPolynomial.monomial_single_add]
    simp

lemma abelianize_expansion (g : FreeAlgebra K Bool) :
    binaryAbelianize K g = (wordCoefficients g).sum
      (fun w c ↦ MvPolynomial.monomial (counts w.toList) c) := by
  rw [binaryAbelianize, lift_eq_word_sum]
  apply Finset.sum_congr rfl
  intro w hw
  dsimp only
  rw [product_X, MvPolynomial.smul_monomial]
  simp

lemma pure_coefficient (g : FreeAlgebra K Bool) (b : Bool) (n : ℕ) :
    MvPolynomial.coeff (Finsupp.single b n) (binaryAbelianize K g) =
      wordCoefficients g (FreeMonoid.ofList (List.replicate n b)) := by
  classical
  rw [abelianize_expansion]
  simp only [Finsupp.sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  have heq (w : FreeMonoid Bool) : counts w.toList = Finsupp.single b n ↔
      w = FreeMonoid.ofList (List.replicate n b) := by
    rw [counts_eq_single]
    exact FreeMonoid.toList.injective.eq_iff.symm
  simp_rw [heq]
  by_cases h : wordCoefficients g (FreeMonoid.ofList (List.replicate n b)) = 0 <;> simp [h]

/-- Every occupied word contains both letters. -/
theorem support_contains_both (g : FreeAlgebra K Bool) (hg : binaryAbelianize K g = 0)
    (w : FreeMonoid Bool) (hw : w ∈ (wordCoefficients g).support) :
    false ∈ w.toList ∧ true ∈ w.toList := by
  have hcoeff : wordCoefficients g w ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hpure (b : Bool) (n : ℕ) :
      wordCoefficients g (FreeMonoid.ofList (List.replicate n b)) = 0 := by
    rw [← pure_coefficient, hg]
    simp
  constructor
  · by_contra hf
    have hrep : w.toList = List.replicate w.toList.length true :=
      List.eq_replicate_of_mem (by intro b hb; cases b <;> simp_all)
    have hwrep : w = FreeMonoid.ofList (List.replicate w.toList.length true) :=
      FreeMonoid.toList.injective hrep
    apply hcoeff
    conv_lhs => rw [hwrep]
    exact hpure true w.toList.length
  · by_contra ht
    have hrep : w.toList = List.replicate w.toList.length false :=
      List.eq_replicate_of_mem (by intro b hb; cases b <;> simp_all)
    have hwrep : w = FreeMonoid.ofList (List.replicate w.toList.length false) :=
      FreeMonoid.toList.injective hrep
    apply hcoeff
    conv_lhs => rw [hwrep]
    exact hpure false w.toList.length

/-- The commutator-kernel support has at least one occurrence of each letter. -/
theorem support_word_length_ge_two (g : FreeAlgebra K Bool)
    (hg : binaryAbelianize K g = 0) (w : FreeMonoid Bool)
    (hw : w ∈ (wordCoefficients g).support) :
    2 ≤ w.toList.length := by
  obtain ⟨hf, ht⟩ := support_contains_both g hg w hw
  cases hL : w.toList with
  | nil => simp [hL] at hf
  | cons b tail =>
    have hother : (if b then false else true) ∈ tail := by
      cases b with
      | false => simpa [hL] using ht
      | true => simpa [hL] using hf
    cases tail with
    | nil => simp at hother
    | cons c rest => simp

/-- A nonzero element of the binary commutator kernel has word degree at least two. -/
theorem wordDegree_ge_two_of_abelianize_zero
    (g : FreeAlgebra K Bool) (hg0 : g ≠ 0)
    (hg : binaryAbelianize K g = 0) : 2 ≤ wordDegree g := by
  classical
  have hwc : wordCoefficients g ≠ 0 := by
    intro h
    apply hg0
    apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
    simpa [wordCoefficients] using h
  obtain ⟨w, hw⟩ := Finsupp.support_nonempty_iff.mpr hwc
  exact (support_word_length_ge_two g hg w hw).trans
    (degreeBound_wordDegree g w hw)
end MakarLimanov.BinarySupport
