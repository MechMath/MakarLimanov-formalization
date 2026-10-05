import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic

/-!
# Matrices with one-sided coordinate bounds

Rows are output indices. The two opposite coordinate bounds force every intermediate
index in a matrix product into a finite rectangle, even for matrices that are not
row-finite or column-finite.
-/

namespace MakarLimanov.ControlledMatrix

variable {K : Type*} {P : ℤ × ℤ → Prop}

/-- An arbitrary subset of the integer coordinate plane. -/
abbrev Index (P : ℤ × ℤ → Prop) := {v : ℤ × ℤ // P v}

/-- Entries obey an upper bound in the first coordinate and a lower bound in the second. -/
def HasBound [Zero K] (A : Matrix (Index P) (Index P) K) (R : ℤ) : Prop :=
  ∀ i j, A i j ≠ 0 → i.val.1 - j.val.1 ≤ R ∧ -R ≤ i.val.2 - j.val.2

/-- Matrices with a uniform finite coordinate bound. -/
def IsControlled [Zero K] (A : Matrix (Index P) (Index P) K) : Prop :=
  ∃ R : ℤ, HasBound A R

/-- Intermediate indices of a two-factor product lie in a finite rectangle. -/
theorem finite_intermediate [Zero K] (A B : Matrix (Index P) (Index P) K)
    {R S : ℤ} (hA : HasBound A R) (hB : HasBound B S) (i j : Index P) :
    {k : Index P | A i k ≠ 0 ∧ B k j ≠ 0}.Finite := by
  have hrect : (Set.Icc (i.val.1 - R) (j.val.1 + S) ×ˢ
      Set.Icc (j.val.2 - S) (i.val.2 + R)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hpre := hrect.preimage (f := fun k : Index P ↦ k.val)
    Subtype.val_injective.injOn
  apply hpre.subset
  intro k hk
  obtain ⟨ha, hc⟩ := hA i k hk.1
  obtain ⟨hb, hd⟩ := hB k j hk.2
  change (i.val.1 - R ≤ k.val.1 ∧ k.val.1 ≤ j.val.1 + S) ∧
    (j.val.2 - S ≤ k.val.2 ∧ k.val.2 ≤ i.val.2 + R)
  omega

/-- A coordinate rectangle has finitely many indices in any subtype. -/
theorem finite_rectangle (a b c d : ℤ) :
    {k : Index P | a ≤ k.val.1 ∧ k.val.1 ≤ b ∧ c ≤ k.val.2 ∧ k.val.2 ≤ d}.Finite := by
  have h := ((Set.finite_Icc a b).prod (Set.finite_Icc c d)).preimage
    (f := fun k : Index P ↦ k.val) Subtype.val_injective.injOn
  exact h.subset fun _ hk ↦ ⟨⟨hk.1, hk.2.1⟩, hk.2.2⟩

section Semiring

variable [Semiring K]

/-- Entrywise finite-sum multiplication, used only on controlled matrices. -/
noncomputable def product (A B : Matrix (Index P) (Index P) K) :
    Matrix (Index P) (Index P) K := fun i j ↦ ∑ᶠ k, A i k * B k j

theorem finite_product_support (A B : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) (i j : Index P) :
    (Function.support fun k ↦ A i k * B k j).Finite := by
  obtain ⟨R, hR⟩ := hA
  obtain ⟨S, hS⟩ := hB
  apply (finite_intermediate A B hR hS i j).subset
  intro k hk
  exact ⟨left_ne_zero_of_mul hk, right_ne_zero_of_mul hk⟩

theorem product_bound (A B : Matrix (Index P) (Index P) K)
    {R S : ℤ} (hA : HasBound A R) (hB : HasBound B S) :
    HasBound (product A B) (R + S) := by
  intro i j hij
  have hex : ∃ k, A i k * B k j ≠ 0 := by
    by_contra! h
    exact hij (by simp [product, h])
  obtain ⟨k, hk⟩ := hex
  obtain ⟨ha, hc⟩ := hA i k (left_ne_zero_of_mul hk)
  obtain ⟨hb, hd⟩ := hB k j (right_ne_zero_of_mul hk)
  constructor <;> omega

theorem product_controlled (A B : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) : IsControlled (product A B) := by
  obtain ⟨R, hR⟩ := hA
  obtain ⟨S, hS⟩ := hB
  exact ⟨R + S, product_bound A B hR hS⟩

/-- Joint support for a three-factor product is finite. -/
theorem finite_triple_support (A B C : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) (hC : IsControlled C)
    (i j : Index P) :
    (Function.support fun kl : Index P × Index P ↦ A i kl.1 * B kl.1 kl.2 * C kl.2 j).Finite := by
  obtain ⟨R, hR⟩ := hA
  obtain ⟨S, hS⟩ := hB
  obtain ⟨T, hT⟩ := hC
  apply ((finite_rectangle (P := P) (i.val.1 - R) (j.val.1 + S + T)
      (j.val.2 - S - T) (i.val.2 + R)).prod
    (finite_rectangle (P := P) (i.val.1 - R - S) (j.val.1 + T)
      (j.val.2 - T) (i.val.2 + R + S))).subset
  intro kl hkl
  have hAB := left_ne_zero_of_mul hkl
  obtain ⟨ha, hc⟩ := hR i kl.1 (left_ne_zero_of_mul hAB)
  obtain ⟨hb, hd⟩ := hS kl.1 kl.2 (right_ne_zero_of_mul hAB)
  obtain ⟨he, hf⟩ := hT kl.2 j (right_ne_zero_of_mul hkl)
  change (_ ∧ _ ∧ _ ∧ _) ∧ (_ ∧ _ ∧ _ ∧ _)
  omega

theorem product_assoc (A B C : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) (hC : IsControlled C) :
    product (product A B) C = product A (product B C) := by
  ext i j
  have ht := finite_triple_support A B C hA hB hC i j
  have hs : (Function.support fun lk : Index P × Index P ↦
      A i lk.2 * B lk.2 lk.1 * C lk.1 j).Finite := by
    exact ht.preimage (f := Prod.swap) (Equiv.prodComm _ _).injective.injOn
  simp only [product]
  simp_rw [finsum_mul' _ _ (finite_product_support A B hA hB _ _),
    mul_finsum' _ _ (finite_product_support B C hB hC _ _)]
  simp_rw [← mul_assoc]
  rw [← finsum_curry _ hs, ← finsum_curry _ ht]
  exact finsum_eq_of_bijective Prod.swap (Equiv.prodComm _ _).bijective
    (fun _ ↦ rfl)

theorem zero_bound : HasBound (0 : Matrix (Index P) (Index P) K) 0 := by
  simp [HasBound]

theorem add_bound (A B : Matrix (Index P) (Index P) K)
    {R S : ℤ} (hA : HasBound A R) (hB : HasBound B S) :
    HasBound (A + B) (max R S) := by
  intro i j hij
  by_cases ha : A i j = 0
  · have hb : B i j ≠ 0 := by simpa [ha] using hij
    obtain ⟨hb₁, hb₂⟩ := hB i j hb
    constructor <;> omega
  · obtain ⟨ha₁, ha₂⟩ := hA i j ha
    constructor <;> omega

theorem add_controlled (A B : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) : IsControlled (A + B) := by
  obtain ⟨R, hR⟩ := hA
  obtain ⟨S, hS⟩ := hB
  exact ⟨max R S, add_bound A B hR hS⟩

/-- A scalar diagonal matrix on the infinite index set. -/
noncomputable def scalarMatrix (a : K) : Matrix (Index P) (Index P) K :=
  fun i j ↦ if i = j then a else 0

theorem scalar_bound (a : K) : HasBound (scalarMatrix (P := P) a) 0 := by
  classical
  intro i j hij
  have h : i = j := by by_contra h; simp [scalarMatrix, h] at hij
  subst j
  simp

theorem scalar_product (a : K) (A : Matrix (Index P) (Index P) K) :
    product (scalarMatrix a) A = fun i j ↦ a * A i j := by
  classical
  ext i j
  rw [product, finsum_eq_single _ i]
  · simp [scalarMatrix]
  · intro k hk
    simp [scalarMatrix, Ne.symm hk]

theorem product_scalar (a : K) (A : Matrix (Index P) (Index P) K) :
    product A (scalarMatrix a) = fun i j ↦ A i j * a := by
  classical
  ext i j
  rw [product, finsum_eq_single _ j]
  · simp [scalarMatrix]
  · intro k hk
    simp [scalarMatrix, hk]

theorem product_add (A B C : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) (hC : IsControlled C) :
    product A (B + C) = product A B + product A C := by
  ext i j
  simp only [product, Matrix.add_apply, mul_add]
  exact finsum_add_distrib (finite_product_support A B hA hB i j)
    (finite_product_support A C hA hC i j)

theorem add_product (A B C : Matrix (Index P) (Index P) K)
    (hA : IsControlled A) (hB : IsControlled B) (hC : IsControlled C) :
    product (A + B) C = product A C + product B C := by
  ext i j
  simp only [product, Matrix.add_apply, add_mul]
  exact finsum_add_distrib (finite_product_support A C hA hC i j)
    (finite_product_support B C hB hC i j)

end Semiring

section Ring

variable [Ring K]

theorem neg_bound (A : Matrix (Index P) (Index P) K) {R : ℤ}
    (hA : HasBound A R) : HasBound (-A) R := by
  intro i j hij
  exact hA i j (by simpa using hij)

/-- A matrix together with the existence of a uniform coordinate bound. -/
structure Controlled (P : ℤ × ℤ → Prop) (K : Type*) [Zero K] where
  entries : Matrix (Index P) (Index P) K
  controlled : IsControlled entries

namespace Controlled

instance : CoeFun (Controlled P K) (fun _ ↦ Index P → Index P → K) := ⟨entries⟩

@[ext]
theorem ext {A B : Controlled P K} (h : ∀ i j, A i j = B i j) : A = B := by
  cases A
  cases B
  congr
  funext i j
  exact h i j

instance : Zero (Controlled P K) := ⟨⟨0, ⟨0, zero_bound⟩⟩⟩

instance : Add (Controlled P K) := ⟨fun A B ↦
  ⟨A.entries + B.entries, add_controlled _ _ A.controlled B.controlled⟩⟩

instance : Neg (Controlled P K) := ⟨fun A ↦
  ⟨-A.entries, by obtain ⟨R, hR⟩ := A.controlled; exact ⟨R, neg_bound _ hR⟩⟩⟩

noncomputable instance : Mul (Controlled P K) := ⟨fun A B ↦
  ⟨product A.entries B.entries, product_controlled _ _ A.controlled B.controlled⟩⟩

noncomputable instance : One (Controlled P K) := ⟨⟨scalarMatrix 1, ⟨0, scalar_bound 1⟩⟩⟩

@[simp] theorem zero_apply (i j : Index P) : (0 : Controlled P K) i j = 0 := rfl
@[simp] theorem add_apply (A B : Controlled P K) (i j : Index P) :
    (A + B) i j = A i j + B i j := rfl
@[simp] theorem neg_apply (A : Controlled P K) (i j : Index P) :
    (-A) i j = -A i j := rfl
theorem mul_apply (A B : Controlled P K) (i j : Index P) :
    (A * B) i j = ∑ᶠ k, A i k * B k j := rfl

noncomputable instance : Ring (Controlled P K) := Ring.ofMinimalAxioms
  (by intros; ext; simp [add_assoc])
  (by intro; ext; simp)
  (by intro; ext; simp)
  (by intro A B C; apply ext; intro i j; exact congrFun (congrFun
    (product_assoc _ _ _ A.controlled B.controlled C.controlled) _) _)
  (by intro A; apply ext; intro i j; change product (scalarMatrix 1) A.entries i j = _
      rw [scalar_product]; simp)
  (by intro A; apply ext; intro i j; change product A.entries (scalarMatrix 1) i j = _
      rw [product_scalar]; simp)
  (by intro A B C; apply ext; intro i j; exact congrFun (congrFun
    (product_add _ _ _ A.controlled B.controlled C.controlled) _) _)
  (by intro A B C; apply ext; intro i j; exact congrFun (congrFun
    (add_product _ _ _ A.controlled B.controlled C.controlled) _) _)

@[simp] theorem entries_one : (1 : Controlled P K).entries = scalarMatrix 1 := rfl

@[simp] theorem entries_add (A B : Controlled P K) :
    (A + B).entries = A.entries + B.entries := rfl

@[simp] theorem entries_mul (A B : Controlled P K) :
    (A * B).entries = product A.entries B.entries := rfl

/-- Scalars act by diagonal matrices. -/
noncomputable def scalarHom : K →+* Controlled P K where
  toFun a := ⟨scalarMatrix a, ⟨0, scalar_bound a⟩⟩
  map_zero' := by ext i j; simp [scalarMatrix]
  map_one' := rfl
  map_add' a b := by
    classical
    ext i j
    change scalarMatrix (a + b) i j = scalarMatrix a i j + scalarMatrix b i j
    by_cases h : i = j <;> simp [scalarMatrix, h]
  map_mul' a b := by
    classical
    ext i j
    change scalarMatrix (a * b) i j = product (scalarMatrix a) (scalarMatrix b) i j
    rw [scalar_product]
    by_cases h : i = j <;> simp [scalarMatrix, h]

end Controlled

end Ring

namespace Controlled

variable [CommRing K]

noncomputable instance : Algebra K (Controlled P K) :=
  (scalarHom (P := P) (K := K)).toAlgebra' (by
    intro a A
    ext i j
    change product (scalarMatrix a) A.entries i j = product A.entries (scalarMatrix a) i j
    rw [scalar_product, product_scalar]
    exact mul_comm _ _)

@[simp]
theorem algebraMap_apply (a : K) (i j : Index P) :
    algebraMap K (Controlled P K) a i j = scalarMatrix a i j := rfl

end Controlled

section Compression

variable [Semiring K] {ι : Type*} [Fintype ι]

/-- Restrict an infinite matrix to a finite family of distinct indices. -/
def compress (e : ι ↪ Index P) (A : Matrix (Index P) (Index P) K) : Matrix ι ι K :=
  fun i j ↦ A (e i) (e j)

/-- Compression preserves a product entry when no contributing intermediate index escapes. -/
theorem compress_product_entry (e : ι ↪ Index P)
    (A B : Matrix (Index P) (Index P) K) (i j : ι)
    (hclosed : ∀ k, A (e i) k ≠ 0 → B k (e j) ≠ 0 → k ∈ Set.range e) :
    compress e (product A B) i j = (compress e A * compress e B) i j := by
  classical
  change (∑ᶠ k, A (e i) k * B k (e j)) = ∑ k, A (e i) (e k) * B (e k) (e j)
  rw [← finsum_eq_sum_of_fintype,
    ← finsum_mem_range (f := fun k ↦ A (e i) k * B k (e j)) e.injective]
  apply finsum_congr
  intro k
  by_cases hk : k ∈ Set.range e
  · simp [hk]
  · have hz : A (e i) k * B k (e j) = 0 := by
      by_contra hn
      exact hk (hclosed k (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn))
    simp [hk, hz]

omit [Fintype ι] in
/-- Entries of sufficiently negative first-coordinate order vanish on a finite square. -/
theorem compress_zero_of_negative_bound (e : ι ↪ Index P)
    (A : Matrix (Index P) (Index P) K) {N T : ℤ}
    (hA : HasBound A (-T)) (hNT : N ≤ T)
    (he : ∀ i, 0 ≤ (e i).val.1 ∧ (e i).val.1 < N) : compress e A = 0 := by
  ext i j
  by_contra hij
  have hn : A (e i) (e j) ≠ 0 := hij
  have hb := (hA _ _ hn).1
  have hi := he i
  have hj := he j
  omega

end Compression

/-- Summing a one-sided step bound along any finite interval of a path. -/
theorem path_interval_le (v : ℕ → ℤ) (R : ℤ) {m : ℕ}
    (hstep : ∀ t < m, v (t + 1) ≤ v t + R) (a n : ℕ) (han : a + n ≤ m) :
    v (a + n) ≤ v a + (n : ℤ) * R := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (by omega)
    have hs := hstep (a + n) (by omega)
    calc
      v (a + (n + 1)) ≤ v (a + n) + R := by simpa [Nat.add_assoc] using hs
      _ ≤ v a + (n : ℤ) * R + R := by omega
      _ = v a + ((n + 1 : ℕ) : ℤ) * R := by push_cast; ring

/-- Both endpoints bound every intermediate index of a controlled path. -/
theorem path_coordinate_bounds (u : ℕ → Index P) (R : ℤ) {m t : ℕ}
    (hstep : ∀ s < m, (u (s + 1)).val.1 - (u s).val.1 ≤ R ∧
      -R ≤ (u (s + 1)).val.2 - (u s).val.2) (ht : t ≤ m) :
    (u m).val.1 - ((m - t : ℕ) : ℤ) * R ≤ (u t).val.1 ∧
    (u t).val.1 ≤ (u 0).val.1 + (t : ℤ) * R ∧
    (u 0).val.2 - (t : ℤ) * R ≤ (u t).val.2 ∧
    (u t).val.2 ≤ (u m).val.2 + ((m - t : ℕ) : ℤ) * R := by
  have ha : ∀ s < m, (u (s + 1)).val.1 ≤ (u s).val.1 + R := by
    intro s hs
    have := (hstep s hs).1
    omega
  have hc : ∀ s < m, -(u (s + 1)).val.2 ≤ -(u s).val.2 + R := by
    intro s hs
    have := (hstep s hs).2
    omega
  have ha₀ := path_interval_le (fun s ↦ (u s).val.1) R ha 0 t (by omega)
  have ha₁ := path_interval_le (fun s ↦ (u s).val.1) R ha t (m - t) (by omega)
  have hc₀ := path_interval_le (fun s ↦ -(u s).val.2) R hc 0 t (by omega)
  have hc₁ := path_interval_le (fun s ↦ -(u s).val.2) R hc t (m - t) (by omega)
  simp only [Nat.zero_add, Nat.add_sub_of_le ht] at ha₀ ha₁ hc₀ hc₁
  omega

/-- Common input and output strips confine every path of length at most D to the square. -/
theorem path_stays_in_square (u : ℕ → Index P) {R N : ℤ} {D m t : ℕ}
    (hR : 0 ≤ R) (hm : m ≤ D) (ht : t ≤ m)
    (hstep : ∀ s < m, (u (s + 1)).val.1 - (u s).val.1 ≤ R ∧
      -R ≤ (u (s + 1)).val.2 - (u s).val.2)
    (hin : (u 0).val.1 < N - (D : ℤ) * R ∧ (D : ℤ) * R ≤ (u 0).val.2)
    (hout : (D : ℤ) * R ≤ (u m).val.1 ∧ (u m).val.2 < N - (D : ℤ) * R) :
    0 ≤ (u t).val.1 ∧ (u t).val.1 < N ∧
    0 ≤ (u t).val.2 ∧ (u t).val.2 < N := by
  obtain ⟨ha₁, ha₂, hc₁, hc₂⟩ := path_coordinate_bounds u R hstep ht
  have htD : (t : ℤ) ≤ D := by omega
  have hmtD : ((m - t : ℕ) : ℤ) ≤ D := by omega
  have hp := mul_le_mul_of_nonneg_right htD hR
  have hq := mul_le_mul_of_nonneg_right hmtD hR
  omega

/-- Nonzero matrix factors give precisely the step hypotheses of square confinement. -/
theorem nonzero_path_stays_in_square [Zero K]
    (u : ℕ → Index P) (A : ℕ → Matrix (Index P) (Index P) K)
    {R N : ℤ} {D m t : ℕ} (hR : 0 ≤ R) (hm : m ≤ D) (ht : t ≤ m)
    (hbound : ∀ s < m, HasBound (A s) R)
    (hpath : ∀ s < m, A s (u (s + 1)) (u s) ≠ 0)
    (hin : (u 0).val.1 < N - (D : ℤ) * R ∧ (D : ℤ) * R ≤ (u 0).val.2)
    (hout : (D : ℤ) * R ≤ (u m).val.1 ∧ (u m).val.2 < N - (D : ℤ) * R) :
    0 ≤ (u t).val.1 ∧ (u t).val.1 < N ∧
    0 ≤ (u t).val.2 ∧ (u t).val.2 < N :=
  path_stays_in_square u hR hm ht
    (fun s hs ↦ hbound s hs _ _ (hpath s hs)) hin hout

end MakarLimanov.ControlledMatrix
