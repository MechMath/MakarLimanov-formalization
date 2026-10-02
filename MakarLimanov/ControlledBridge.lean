import MakarLimanov.ControlledMatrix
import MakarLimanov.Lattice
import MakarLimanov.NormalOrdering

/-!
# Concrete controlled matrices for Laurent monomial operators

A weighted shift acts on each basis vector by a scalar times one basis vector.
Its product formula provides the finite-sum matrix realization of multiplication
by Laurent monomials used in Section 6 of the paper.
-/

namespace MakarLimanov.ControlledMatrix

variable {K : Type*} {P : ℤ × ℤ → Prop} [Ring K]

/-- A matrix with at most one nonzero entry in each column. -/
noncomputable def weightedShift (e : Index P → Index P) (w : Index P → K) :
    Matrix (Index P) (Index P) K := fun i j ↦ if i = e j then w j else 0

/-- A bound on the displacement of nonzero weights controls the entire matrix. -/
theorem weightedShift_bound (e : Index P → Index P) (w : Index P → K) (R : ℤ)
    (h : ∀ j, w j ≠ 0 → (e j).val.1 - j.val.1 ≤ R ∧
      -R ≤ (e j).val.2 - j.val.2) : HasBound (weightedShift e w) R := by
  classical
  intro i j hij
  by_cases he : i = e j
  · subst i
    exact h j (by simpa [weightedShift] using hij)
  · simp [weightedShift, he] at hij

/-- Multiplication of weighted shifts is composition, with the transported weight. -/
theorem weightedShift_product (e f : Index P → Index P) (w v : Index P → K) :
    product (weightedShift e w) (weightedShift f v) =
      weightedShift (e ∘ f) (fun j ↦ w (f j) * v j) := by
  classical
  ext i j
  rw [product, finsum_eq_single _ (f j)]
  · by_cases h : i = e (f j) <;> simp [weightedShift, h]
  · intro k hk
    simp [weightedShift, hk]

/-- A controlled matrix obtained from a bounded weighted shift. -/
noncomputable def shift (e : Index P → Index P) (w : Index P → K) (R : ℤ)
    (h : ∀ j, w j ≠ 0 → (e j).val.1 - j.val.1 ≤ R ∧
      -R ≤ (e j).val.2 - j.val.2) : Controlled P K :=
  ⟨weightedShift e w, R, weightedShift_bound e w R h⟩

@[simp] theorem shift_apply (e : Index P → Index P) (w : Index P → K) (R : ℤ)
    (h : ∀ j, w j ≠ 0 → (e j).val.1 - j.val.1 ≤ R ∧
      -R ≤ (e j).val.2 - j.val.2) (i j : Index P) :
    shift e w R h i j = if i = e j then w j else 0 := rfl

/-- Bounds add under powers in the controlled matrix ring. -/
theorem controlled_pow_bound (A : Controlled P K) {R : ℤ}
    (hA : HasBound A.entries R) (n : ℕ) : HasBound (A ^ n).entries ((n : ℤ) * R) := by
  induction n with
  | zero =>
      simpa only [pow_zero, Nat.cast_zero, zero_mul] using (scalar_bound (P := P) (1 : K))
  | succ n ih =>
      have h := product_bound (A ^ n).entries A.entries ih hA
      simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using h

end MakarLimanov.ControlledMatrix

namespace MakarLimanov.Lattice

open ControlledMatrix

variable {K : Type*} [Ring K] (p : ℕ)

/-- Multiplication by `z^(r/p)` shifts the first lattice coordinate by `r`. -/
def zShift (r : ℤ) (j : Index (InLattice p)) : Index (InLattice p) :=
  ⟨(j.val.1 + r, j.val.2 - r), by
    constructor
    · have h := j.property.1; change 0 ≤ j.val.1 + j.val.2 at h; dsimp; omega
    · have h := j.property.2; change (p : ℤ) ∣ j.val.1 + j.val.2 at h
      dsimp; convert h using 1; ring⟩

@[simp] theorem zShift_val (r : ℤ) (j : Index (InLattice p)) :
    (zShift p r j).val = (j.val.1 + r, j.val.2 - r) := rfl

@[simp] theorem zShift_add (r s : ℤ) (j : Index (InLattice p)) :
    zShift p r (zShift p s j) = zShift p (r+s) j := by
  apply Subtype.ext
  simp only [zShift_val, Prod.mk.injEq]
  constructor <;> ring

@[simp] theorem zShift_zero (j : Index (InLattice p)) : zShift p 0 j = j := by
  apply Subtype.ext
  simp [zShift]

/-- The concrete controlled matrix of multiplication by a Laurent monomial. -/
noncomputable def zMatrix (r : ℤ) : Controlled (InLattice p) K :=
  shift (zShift p r) (fun _ ↦ 1) r (by intro j _; simp [zShift])

@[simp] theorem zMatrix_apply (r : ℤ) (i j : Index (InLattice p)) :
    zMatrix (K := K) p r i j = if i = zShift p r j then 1 else 0 := rfl

/-- A Laurent monomial has exactly its exponent as coordinate bound. -/
theorem zMatrix_bound (r : ℤ) : HasBound (zMatrix (K := K) p r).entries r :=
  weightedShift_bound _ _ _ (by intro j _; simp [zShift])

@[simp] theorem zMatrix_mul (r s : ℤ) :
    zMatrix (K := K) p r * zMatrix p s = zMatrix p (r+s) := by
  apply Controlled.ext
  intro i j
  change product (weightedShift (zShift p r) (fun _ ↦ (1 : K)))
    (weightedShift (zShift p s) (fun _ ↦ (1 : K))) i j = _
  rw [weightedShift_product]
  simp [weightedShift]

@[simp] theorem zMatrix_zero : zMatrix (K := K) p 0 = 1 := by
  apply Controlled.ext
  intro i j
  change (if i = zShift p 0 j then (1 : K) else 0) = scalarMatrix 1 i j
  simp [scalarMatrix]

/-- Multiplication by `w` increases the second lattice coordinate by `p`. -/
def wShift (j : Index (InLattice p)) : Index (InLattice p) :=
  ⟨(j.val.1, j.val.2 + p), by
    constructor
    · have h := j.property.1; change 0 ≤ j.val.1 + j.val.2 at h; dsimp; omega
    · have h := j.property.2; change (p : ℤ) ∣ j.val.1 + j.val.2 at h
      change (p : ℤ) ∣ j.val.1 + (j.val.2 + p)
      rw [← add_assoc]; exact dvd_add h (dvd_refl _)⟩

@[simp] theorem wShift_val (j : Index (InLattice p)) :
    (wShift p j).val = (j.val.1, j.val.2 + p) := rfl

/-- The concrete controlled matrix of multiplication by `w`. -/
noncomputable def wMatrix : Controlled (InLattice p) K :=
  shift (wShift p) (fun _ ↦ 1) 0 (by intro j _; simp [wShift])

/-- Multiplication by `w` has coordinate bound zero. -/
theorem wMatrix_bound : HasBound (wMatrix (K := K) p).entries 0 :=
  weightedShift_bound _ _ _ (by intro j _; simp [wShift])

@[simp] theorem zShift_wShift (r : ℤ) (j : Index (InLattice p)) :
    zShift p r (wShift p j) = wShift p (zShift p r j) := by
  apply Subtype.ext
  simp only [zShift_val, wShift_val, Prod.mk.injEq]
  exact ⟨trivial, by ring⟩

/-- The Laurent and polynomial multiplication matrices commute. -/
theorem zMatrix_commute_wMatrix (r : ℤ) :
    Commute (zMatrix (K := K) p r) (wMatrix p) := by
  change zMatrix p r * wMatrix p = wMatrix p * zMatrix p r
  apply Controlled.ext
  intro i j
  change product (weightedShift (zShift p r) (fun _ ↦ (1 : K)))
    (weightedShift (wShift p) (fun _ ↦ (1 : K))) i j =
    product (weightedShift (wShift p) (fun _ ↦ (1 : K)))
      (weightedShift (zShift p r) (fun _ ↦ (1 : K))) i j
  rw [weightedShift_product, weightedShift_product]
  simp [weightedShift]

section Differential

variable {F : Type*} [Field F]

/-- The matrix of the first summand `-∂z` in the normal-ordering operator. -/
noncomputable def dzMatrix : Controlled (InLattice p) F :=
  shift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F)) (-(p : ℤ))
    (by intro j _; simp [zShift])

/-- Differentiation in `z` lowers the scaled order by `p`. -/
theorem dzMatrix_bound : HasBound (dzMatrix (F := F) p).entries (-(p : ℤ)) :=
  weightedShift_bound _ _ _ (by intro j _; simp [zShift])

/-- The actual matrices of multiplication by `z` and `-∂z` obey the Weyl relation. -/
theorem zMatrix_dzMatrix_commutator (hp : 0 < p) [CharZero F] :
    zMatrix (K := F) p (p : ℤ) * dzMatrix p -
      dzMatrix p * zMatrix p (p : ℤ) = 1 := by
  have hpF : (p : F) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hp)
  apply Controlled.ext
  intro i j
  change ((zMatrix (K := F) p (p : ℤ) * dzMatrix p -
    dzMatrix p * zMatrix p (p : ℤ)) : Controlled (InLattice p) F) i j = (1 : Controlled (InLattice p) F) i j
  simp only [sub_eq_add_neg, Controlled.add_apply, Controlled.neg_apply]
  change product (weightedShift (zShift p (p : ℤ)) (fun _ ↦ (1 : F)))
      (weightedShift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F))) i j +
    -product (weightedShift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F)))
      (weightedShift (zShift p (p : ℤ)) (fun _ ↦ (1 : F))) i j = scalarMatrix 1 i j
  rw [weightedShift_product, weightedShift_product]
  by_cases hij : i = j
  · subst i
    simp [weightedShift, zShift, scalarMatrix]
    field_simp
    ring
  · simp [weightedShift, scalarMatrix, hij]

/-- The exponent of `w` in the basis vector indexed by the lattice point. -/
def wDegree (j : Index (InLattice p)) : ℤ := (j.val.1 + j.val.2) / (p : ℤ)

@[simp] theorem wDegree_zShift (r : ℤ) (j : Index (InLattice p)) :
    wDegree p (zShift p r j) = wDegree p j := by
  unfold wDegree zShift
  congr 1
  ring

/-- The second summand of the differential operator lowers the `w` degree when possible. -/
def downShift (j : Index (InLattice p)) : Index (InLattice p) :=
  if h : (p : ℤ) ≤ j.val.1 + j.val.2 then
    ⟨(j.val.1 - p, j.val.2), by
      constructor
      · dsimp; omega
      · have hj := j.property.2
        change (p : ℤ) ∣ j.val.1 + j.val.2 at hj
        convert dvd_sub hj (dvd_refl (p : ℤ)) using 1; dsimp; ring⟩
  else j

@[simp] theorem downShift_zShift (r : ℤ) (j : Index (InLattice p)) :
    downShift p (zShift p r j) = zShift p r (downShift p j) := by
  by_cases h : (p : ℤ) ≤ j.val.1 + j.val.2
  · apply Subtype.ext
    simp [downShift, zShift, h]
    ring
  · simp [downShift, zShift, h]

/-- The matrix of `-z⁻¹∂w`; its weight kills the bottom `w` degree. -/
noncomputable def dwMatrix : Controlled (InLattice p) F :=
  shift (downShift p) (fun j ↦ -(wDegree p j : F)) 0 (by
    intro j _
    unfold downShift
    split_ifs <;> dsimp <;> constructor <;> omega)

/-- The mixed derivative term has coordinate bound zero. -/
theorem dwMatrix_bound : HasBound (dwMatrix (F := F) p).entries 0 := by
  apply weightedShift_bound
  intro j _
  unfold downShift
  split_ifs <;> dsimp <;> constructor <;> omega

/-- Laurent multiplication commutes with the `w` derivative term. -/
theorem zMatrix_commute_dwMatrix (r : ℤ) :
    Commute (zMatrix (K := F) p r) (dwMatrix p) := by
  change zMatrix p r * dwMatrix p = dwMatrix p * zMatrix p r
  apply Controlled.ext
  intro i j
  change product (weightedShift (zShift p r) (fun _ ↦ (1 : F)))
    (weightedShift (downShift p) (fun j ↦ -(wDegree p j : F))) i j =
    product (weightedShift (downShift p) (fun j ↦ -(wDegree p j : F)))
      (weightedShift (zShift p r) (fun _ ↦ (1 : F))) i j
  rw [weightedShift_product, weightedShift_product]
  simp [weightedShift]

/-- The actual normal-ordering operator `-∂z-z⁻¹∂w` on the lattice basis. -/
noncomputable def tMatrix : Controlled (InLattice p) F := dzMatrix p + dwMatrix p

/-- The normal-ordering operator has coordinate bound zero. -/
theorem tMatrix_bound : HasBound (tMatrix (F := F) p).entries 0 := by
  have h := add_bound (dzMatrix (F := F) p).entries (dwMatrix p).entries
    (dzMatrix_bound p) (dwMatrix_bound p)
  simpa [tMatrix, max_eq_right (by omega : -(p : ℤ) ≤ 0)] using h

/-- The concrete normal-ordering operator satisfies its first commutator identity. -/
theorem zMatrix_tMatrix_commutator (hp : 0 < p) [CharZero F] :
    zMatrix (K := F) p (p : ℤ) * tMatrix p -
      tMatrix p * zMatrix p (p : ℤ) = 1 := by
  have hd := zMatrix_dzMatrix_commutator (F := F) p hp
  have hw := (zMatrix_commute_dwMatrix (F := F) p (p : ℤ)).eq
  dsimp [tMatrix]
  rw [mul_add, add_mul, hw]
  simpa only [add_sub_add_right_eq_sub] using hd

@[simp] theorem wDegree_wShift (hp : 0 < p) (j : Index (InLattice p)) :
    wDegree p (wShift p j) = wDegree p j + 1 := by
  have hpz : (p : ℤ) ≠ 0 := by omega
  unfold wDegree wShift
  dsimp
  rw [← add_assoc, Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hpz]

lemma wDegree_zero_of_bottom (hp : 0 < p) (j : Index (InLattice p))
    (h : ¬ (p : ℤ) ≤ j.val.1 + j.val.2) : wDegree p j = 0 := by
  apply Int.ediv_eq_zero_of_lt_abs j.property.1
  rw [abs_of_nonneg (by omega : 0 ≤ (p : ℤ))]
  omega

@[simp] theorem downShift_wShift (j : Index (InLattice p)) :
    downShift p (wShift p j) = zShift p (-(p : ℤ)) j := by
  have hj := j.property.1
  change 0 ≤ j.val.1 + j.val.2 at hj
  have h : (p : ℤ) ≤ j.val.1 + (j.val.2 + p) := by omega
  apply Subtype.ext
  simp [downShift, wShift, zShift, h]
  ring

lemma wShift_downShift (j : Index (InLattice p))
    (h : (p : ℤ) ≤ j.val.1 + j.val.2) :
    wShift p (downShift p j) = zShift p (-(p : ℤ)) j := by
  apply Subtype.ext
  simp [downShift, wShift, zShift, h]
  ring

/-- The `w` derivative term satisfies the second required commutator identity. -/
theorem wMatrix_dwMatrix_commutator (hp : 0 < p) :
    wMatrix (K := F) p * dwMatrix p - dwMatrix p * wMatrix p =
      zMatrix p (-(p : ℤ)) := by
  apply Controlled.ext
  intro i j
  change ((wMatrix p * dwMatrix p - dwMatrix p * wMatrix p) :
    Controlled (InLattice p) F) i j = zMatrix p (-(p : ℤ)) i j
  simp only [sub_eq_add_neg, Controlled.add_apply, Controlled.neg_apply]
  change product (weightedShift (wShift p) (fun _ ↦ (1 : F)))
      (weightedShift (downShift p) (fun j ↦ -(wDegree p j : F))) i j +
    -product (weightedShift (downShift p) (fun j ↦ -(wDegree p j : F)))
      (weightedShift (wShift p) (fun _ ↦ (1 : F))) i j = _
  rw [weightedShift_product, weightedShift_product]
  by_cases h : (p : ℤ) ≤ j.val.1 + j.val.2
  · simp only [weightedShift, Function.comp_apply, wShift_downShift p j h,
      downShift_wShift, wDegree_wShift p hp, Int.cast_add, Int.cast_one,
      one_mul, mul_one, zMatrix_apply]
    split_ifs <;> ring
  · simp only [weightedShift, Function.comp_apply, downShift_wShift,
      wDegree_zero_of_bottom p hp j h, wDegree_wShift p hp, zero_add,
      Int.cast_zero, Int.cast_one, neg_zero, mul_zero, mul_one, ite_self,
      zMatrix_apply, zero_add]
    split_ifs <;> ring

/-- Multiplication by `w` commutes with the pure `z` derivative term. -/
theorem wMatrix_commute_dzMatrix : Commute (wMatrix (K := F) p) (dzMatrix p) := by
  change wMatrix p * dzMatrix p = dzMatrix p * wMatrix p
  apply Controlled.ext
  intro i j
  change product (weightedShift (wShift p) (fun _ ↦ (1 : F)))
    (weightedShift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F))) i j =
    product (weightedShift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F)))
      (weightedShift (wShift p) (fun _ ↦ (1 : F))) i j
  rw [weightedShift_product, weightedShift_product]
  simp [weightedShift, zShift, wShift]

/-- The complete differential operator satisfies the second commutator identity. -/
theorem wMatrix_tMatrix_commutator (hp : 0 < p) :
    wMatrix (K := F) p * tMatrix p - tMatrix p * wMatrix p =
      zMatrix p (-(p : ℤ)) := by
  have hw := wMatrix_dwMatrix_commutator (F := F) p hp
  have hd := (wMatrix_commute_dzMatrix (F := F) p).eq
  dsimp [tMatrix]
  rw [mul_add, add_mul, hd]
  simpa only [add_sub_add_left_eq_sub] using hw

/-- The pure derivative has the expected commutator with every fractional Laurent power. -/
theorem zMatrix_dzMatrix_commutator_general (r : ℤ) :
    zMatrix (K := F) p r * dzMatrix p - dzMatrix p * zMatrix p r =
      algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F)) *
        zMatrix p (r - p) := by
  apply Controlled.ext
  intro i j
  change ((zMatrix (K := F) p r * dzMatrix p - dzMatrix p * zMatrix p r) :
    Controlled (InLattice p) F) i j =
      ((algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F)) *
        zMatrix p (r - p)) : Controlled (InLattice p) F) i j
  simp only [sub_eq_add_neg, Controlled.add_apply, Controlled.neg_apply]
  change product (weightedShift (zShift p r) (fun _ ↦ (1 : F)))
      (weightedShift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F))) i j +
    -product (weightedShift (zShift p (-(p : ℤ))) (fun j ↦ -(j.val.1 : F) / (p : F)))
      (weightedShift (zShift p r) (fun _ ↦ (1 : F))) i j =
    product (scalarMatrix ((r : F) / (p : F)))
      (weightedShift (zShift p (r - p)) (fun _ ↦ (1 : F))) i j
  rw [weightedShift_product, weightedShift_product, scalar_product]
  have h₁ : (fun j ↦ zShift p r (zShift p (-(p : ℤ)) j)) = zShift p (r - p) := by
    funext j
    rw [zShift_add]
    congr 1
  have h₂ : (fun j ↦ zShift p (-(p : ℤ)) (zShift p r j)) = zShift p (r - p) := by
    funext j
    rw [zShift_add]
    congr 1
    ring
  simp only [weightedShift, Function.comp_apply]
  rw [congrFun h₁, congrFun h₂]
  by_cases hij : i = zShift p (r - p) j
  · simp [hij, zShift, add_div, neg_div]
  · simp [hij]

/-- Every fractional Laurent power has the required commutator with the full operator. -/
theorem zMatrix_tMatrix_commutator_general (r : ℤ) :
    zMatrix (K := F) p r * tMatrix p - tMatrix p * zMatrix p r =
      algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F)) *
        zMatrix p (r - p) := by
  have hd := zMatrix_dzMatrix_commutator_general (F := F) p r
  have hw := (zMatrix_commute_dwMatrix (F := F) p r).eq
  dsimp [tMatrix]
  rw [mul_add, add_mul, hw]
  simpa only [add_sub_add_right_eq_sub] using hd

/-- The finite monomial operator used by the paper's normal-order map. -/
noncomputable def normalMonomialMatrix (i j : ℕ) (r : ℤ) : Controlled (InLattice p) F :=
  (tMatrix p) ^ i * (wMatrix p) ^ j * zMatrix p r

/--
Every normal-ordered monomial has the Laurent exponent as a bound, independently
of both Taylor exponents. This permits infinite Taylor tails in the later realization.
-/
theorem normalMonomialMatrix_bound (i j : ℕ) (r : ℤ) :
    HasBound (normalMonomialMatrix (F := F) p i j r).entries r := by
  have ht := controlled_pow_bound (tMatrix (F := F) p) (tMatrix_bound p) i
  have hw := controlled_pow_bound (wMatrix (K := F) p) (wMatrix_bound p) j
  have htw := product_bound ((tMatrix (F := F) p) ^ i).entries
    ((wMatrix (K := F) p) ^ j).entries ht hw
  have h := product_bound (((tMatrix (F := F) p) ^ i) * ((wMatrix p) ^ j)).entries
    (zMatrix (K := F) p r).entries htw (zMatrix_bound p r)
  simpa only [normalMonomialMatrix, mul_zero, zero_add] using h

@[simp] theorem normalMonomialMatrix_zero : normalMonomialMatrix (F := F) p 0 0 0 = 1 := by
  simp [normalMonomialMatrix]

end Differential

end MakarLimanov.Lattice
