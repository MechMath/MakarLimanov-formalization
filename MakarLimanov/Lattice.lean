import MakarLimanov.Compression
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Finite lattice squares used in the matrix compression. -/

namespace MakarLimanov.Lattice
open ControlledMatrix

/-- The index lattice for denominator p. -/
def InLattice (p : ℕ) (v : ℤ × ℤ) : Prop := 0 ≤ v.1 + v.2 ∧ (p : ℤ) ∣ v.1 + v.2

/-- A square is parametrized by a first coordinate and a block of the second coordinate. -/
abbrev Square (p S : ℕ) := Fin (p * S) × Fin S

/-- The unique residue that makes the sum of the two coordinates divisible by p. -/
def residue (p a : ℕ) : ℕ := (p - a % p) % p

lemma residue_lt {p : ℕ} (hp : 0 < p) (a : ℕ) : residue p a < p :=
  Nat.mod_lt _ hp

lemma dvd_add_residue {p : ℕ} (hp : 0 < p) (a : ℕ) : p ∣ a + residue p a := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod]
  unfold residue
  have hm := Nat.mod_lt a hp
  by_cases h : a % p = 0
  · simp [h]
  · have hsub : p - a % p < p := by omega
    rw [Nat.mod_eq_of_lt hsub, Nat.mod_eq_of_lt hsub]
    have heq : a % p + (p - a % p) = p := by omega
    rw [heq, Nat.mod_self]

def coordinates (p S : ℕ) (x : Square p S) : ℤ × ℤ :=
  (x.1.val, p * x.2.val + residue p x.1.val)

lemma coordinates_in_lattice {p S : ℕ} (hp : 0 < p) (x : Square p S) :
    InLattice p (coordinates p S x) := by
  constructor
  · unfold coordinates; positivity
  · have h : p ∣ x.1.val + (p * x.2.val + residue p x.1.val) := by
      convert dvd_add (dvd_add_residue hp x.1.val) (dvd_mul_right p x.2.val) using 1
      omega
    dsimp [coordinates]
    exact_mod_cast h

lemma coordinates_square {p S : ℕ} (hp : 0 < p) (x : Square p S) :
    0 ≤ (coordinates p S x).1 ∧ (coordinates p S x).1 < p * S ∧
    0 ≤ (coordinates p S x).2 ∧ (coordinates p S x).2 < p * S := by
  have hr := residue_lt hp x.1.val
  have hprod : p * (x.2.val + 1) ≤ p * S := Nat.mul_le_mul_left _ x.2.isLt
  have hval : p * x.2.val + residue p x.1.val < p * S := by nlinarith
  dsimp [coordinates]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast x.1.isLt, by positivity, by exact_mod_cast hval⟩

lemma coordinates_injective {p S : ℕ} (hp : 0 < p) :
    Function.Injective (coordinates p S) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have ha : a = c := by
    apply Fin.ext
    have hh := congrArg Prod.fst h
    dsimp [coordinates] at hh
    exact_mod_cast hh
  subst c
  have hb : b = d := by
    apply Fin.ext
    have hh := congrArg Prod.snd h
    dsimp [coordinates] at hh
    have hh' : p * b.val = p * d.val := by exact_mod_cast (add_right_cancel hh)
    exact Nat.eq_of_mul_eq_mul_left hp hh'
  subst d
  rfl

/-- The actual embedding into the infinite lattice. -/
def embedding {p S : ℕ} (hp : 0 < p) : Square p S ↪ Index (InLattice p) where
  toFun x := ⟨coordinates p S x, coordinates_in_lattice hp x⟩
  inj' := fun _ _ h ↦ coordinates_injective hp (congrArg Subtype.val h)

lemma square_card (p S : ℕ) : Fintype.card (Square p S) = p * S ^ 2 := by
  simp [Square, Fintype.card_prod, pow_two, Nat.mul_assoc]

lemma coordinates_surjective_square {p S : ℕ} (hp : 0 < p) (v : Index (InLattice p))
    (hv : 0 ≤ v.val.1 ∧ v.val.1 < p * S ∧ 0 ≤ v.val.2 ∧ v.val.2 < p * S) :
    v ∈ Set.range (embedding (S := S) hp) := by
  let a := v.val.1.toNat
  let c := v.val.2.toNat
  have ha : a < p * S := by dsimp [a]; omega
  have hc : c < p * S := by dsimp [c]; omega
  have hac : p ∣ a + c := by
    have hh := v.property.2
    have hcast : (a : ℤ) + (c : ℤ) = v.val.1 + v.val.2 := by dsimp [a,c]; omega
    rw [← hcast] at hh
    exact_mod_cast hh
  have hres : residue p a = c % p := by
    have hh : Nat.ModEq p (a + residue p a) (a + c) :=
      (Nat.modEq_zero_iff_dvd.mpr (dvd_add_residue hp a)).trans
        (Nat.modEq_zero_iff_dvd.mpr hac).symm
    have hh' := Nat.ModEq.add_left_cancel' a hh
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (residue_lt hp a)] using hh'
  have hdiv : c / p < S := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using hc)
  refine ⟨(⟨a, ha⟩, ⟨c / p, hdiv⟩), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · dsimp [embedding, coordinates, a]; omega
  · dsimp [embedding, coordinates]
    rw [hres]
    have heq : p * (c / p) + c % p = c := by
      simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div c p
    have heq' : (p : ℤ) * (c / p : ℕ) + (c % p : ℕ) = c := by exact_mod_cast heq
    simpa [c, Int.toNat_of_nonneg hv.2.2.1] using heq'
lemma embedding_range {p S : ℕ} (hp : 0 < p) (v : Index (InLattice p)) :
    v ∈ Set.range (embedding (S := S) hp) ↔
      0 ≤ v.val.1 ∧ v.val.1 < p * S ∧ 0 ≤ v.val.2 ∧ v.val.2 < p * S := by
  constructor
  · rintro ⟨x, rfl⟩
    exact coordinates_square hp x
  · exact coordinates_surjective_square hp v

lemma card_low (n B : ℕ) : (Finset.univ.filter (fun a : Fin n ↦ a.val < B)).card ≤ B := by
  rw [Fin.card_filter_val_lt]
  exact Nat.min_le_right _ _

lemma card_high (n B : ℕ) : (Finset.univ.filter (fun a : Fin n ↦ n - B ≤ a.val)).card ≤ B := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun a : Fin n ↦ a.val < n - B)
  simp only [not_lt, Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h
  omega

lemma card_first_low (p S B : ℕ) :
    (Finset.univ.filter (fun x : Square p S ↦ x.1.val < B)).card ≤ B * S := by
  rw [← Finset.univ_product_univ, (Finset.filter_product_left (fun a : Fin (p * S) ↦ a.val < B)), Finset.card_product]
  simpa using Nat.mul_le_mul_right S (card_low (p * S) B)

lemma card_first_high (p S B : ℕ) :
    (Finset.univ.filter (fun x : Square p S ↦ p * S - B ≤ x.1.val)).card ≤ B * S := by
  rw [← Finset.univ_product_univ, (Finset.filter_product_left (fun a : Fin (p * S) ↦ p * S - B ≤ a.val)), Finset.card_product]
  simpa using Nat.mul_le_mul_right S (card_high (p * S) B)

lemma card_second_low (p S B : ℕ) :
    (Finset.univ.filter (fun x : Square p S ↦ x.2.val < B)).card ≤ p * S * B := by
  rw [← Finset.univ_product_univ, (Finset.filter_product_right (fun a : Fin S ↦ a.val < B)), Finset.card_product]
  simpa using Nat.mul_le_mul_left (p * S) (card_low S B)

lemma card_second_high (p S B : ℕ) :
    (Finset.univ.filter (fun x : Square p S ↦ S - B ≤ x.2.val)).card ≤ p * S * B := by
  rw [← Finset.univ_product_univ, (Finset.filter_product_right (fun a : Fin S ↦ S - B ≤ a.val)), Finset.card_product]
  simpa using Nat.mul_le_mul_left (p * S) (card_high S B)
lemma first_fiber_card {p S : ℕ} (hp : 0 < p) (a : ℤ) :
    (Finset.univ.filter (fun x : Square p S ↦ (embedding hp x).val.1 = a)).card ≤ S := by
  classical
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun x : Square p S ↦ (embedding hp x).val.1 = a)) (t := Finset.univ)
    (fun x : Square p S ↦ x.2) (by intro x _; exact Finset.mem_univ _)
    (by
      intro x hx y hy hxy
      apply Prod.ext ?_ hxy
      apply Fin.ext
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [embedding, coordinates] at hx' hy'
      exact_mod_cast hx'.trans hy'.symm)
  simpa using h

lemma second_fiber_card {p S : ℕ} (hp : 0 < p) (c : ℤ) :
    (Finset.univ.filter (fun x : Square p S ↦ (embedding hp x).val.2 = c)).card ≤ S := by
  classical
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun x : Square p S ↦ (embedding hp x).val.2 = c)) (t := Finset.range S)
    (fun x : Square p S ↦ x.1.val / p) (by
      intro x _
      apply Finset.mem_range.mpr
      exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using x.1.isLt))
    (by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have heq : (coordinates p S x).2 = (coordinates p S y).2 := hx'.trans hy'.symm
      have hxdiv := (coordinates_in_lattice hp x).2
      have hydiv := (coordinates_in_lattice hp y).2
      have hdiff : (p : ℤ) ∣ (x.1.val : ℤ) - y.1.val := by
        have hh := dvd_sub hxdiv hydiv
        dsimp [coordinates] at hh heq
        rw [heq] at hh
        simpa using hh
      have hmod : Nat.ModEq p x.1.val y.1.val := (Nat.modEq_iff_dvd.mpr hdiff).symm
      have ha : x.1 = y.1 := by
        apply Fin.ext
        have hxrec := Nat.mod_add_div x.1.val p
        have hyrec := Nat.mod_add_div y.1.val p
        dsimp only at hxy
        change x.1.val % p = y.1.val % p at hmod
        rw [hxy, hmod] at hxrec
        omega
      apply coordinates_injective hp
      apply Prod.ext
      · dsimp [coordinates]; rw [ha]
      · exact heq)
  simpa using h

/-- Concrete dimension and rank estimate on the congruence lattice. -/
theorem compression_rank [Field K] {σ : Type*} {p S T A D : ℕ} (hp : 0 < p)
    (hST : S ≤ T) (f : FreeAlgebra K σ) (hD : DegreeBound f D)
    (X : σ → Controlled (InLattice p) K)
    (hX : ∀ s, HasBound (X s).entries (p * A))
    (hres : HasBound (FreeAlgebra.lift K X f).entries (-(p * T : ℤ))) :
    (FreeAlgebra.lift K (fun s ↦ compress (embedding (S := S) hp) (X s).entries) f).rank ≤
      4 * D * A * p * S := by
  have h := polynomial_compress_rank_le_four (embedding (S := S) hp)
    (R := p * A) (S := S) (N := p * S) (T := p * T)
    (by exact_mod_cast Nat.mul_le_mul_left p hST)
    (embedding_range hp) (first_fiber_card hp) (second_fiber_card hp) f hD X
    (by simpa using hX) hres
  convert h using 1
  ring
end MakarLimanov.Lattice
