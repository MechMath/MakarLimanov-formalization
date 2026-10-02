import MakarLimanov.ControlledBridge

/-!
# Finite source support in the normal-order realization

Exact first-coordinate shifts and two-sided second-coordinate intervals show
that each entry receives only finitely many Taylor monomials when Laurent
exponents have a common upper bound.
-/

namespace MakarLimanov.ControlledMatrix

variable {K : Type*} [Ring K] {P : ℤ × ℤ → Prop}

/-- Exact displacement in the first coordinate and an interval in the second. -/
def HasDisplacement (A : Matrix (Index P) (Index P) K) (a l u : ℤ) : Prop :=
  ∀ i j, A i j ≠ 0 → i.val.1 - j.val.1 = a ∧
    l ≤ i.val.2 - j.val.2 ∧ i.val.2 - j.val.2 ≤ u

lemma displacement_product (A B : Matrix (Index P) (Index P) K)
    {a b l m u v : ℤ} (hA : HasDisplacement A a l u) (hB : HasDisplacement B b m v) :
    HasDisplacement (product A B) (a+b) (l+m) (u+v) := by
  intro i j hij
  have hex : ∃ k, A i k * B k j ≠ 0 := by
    by_contra! h
    exact hij (by simp [product, h])
  obtain ⟨k, hk⟩ := hex
  obtain ⟨ha, hl, hu⟩ := hA i k (left_ne_zero_of_mul hk)
  obtain ⟨hb, hm, hv⟩ := hB k j (right_ne_zero_of_mul hk)
  constructor <;> omega

lemma displacement_one : HasDisplacement (1 : Controlled P K).entries 0 0 0 := by
  classical
  intro i j hij
  change scalarMatrix 1 i j ≠ 0 at hij
  have h : i = j := by by_contra h; simp [scalarMatrix, h] at hij
  subst i
  simp

lemma displacement_pow (A : Controlled P K) {a l u : ℤ}
    (hA : HasDisplacement A.entries a l u) (n : ℕ) :
    HasDisplacement (A ^ n).entries ((n : ℤ)*a) ((n : ℤ)*l) ((n : ℤ)*u) := by
  induction n with
  | zero => simpa using (displacement_one (K := K) (P := P))
  | succ n ih =>
      have h := displacement_product (A ^ n).entries A.entries ih hA
      simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using h

lemma weightedShift_displacement (e : Index P → Index P) (w : Index P → K)
    (a l u : ℤ) (h : ∀ j, w j ≠ 0 → (e j).val.1 - j.val.1 = a ∧
      l ≤ (e j).val.2 - j.val.2 ∧ (e j).val.2 - j.val.2 ≤ u) :
    HasDisplacement (weightedShift e w) a l u := by
  classical
  intro i j hij
  by_cases he : i = e j
  · subst i
    exact h j (by simpa [weightedShift] using hij)
  · simp [weightedShift, he] at hij

end MakarLimanov.ControlledMatrix

namespace MakarLimanov.Lattice

open ControlledMatrix

variable {F : Type*} [Field F] (p : ℕ)

lemma zMatrix_displacement (r : ℤ) :
    HasDisplacement (zMatrix (K := F) p r).entries r (-r) (-r) := by
  apply weightedShift_displacement
  intro j _
  simp [zShift]

lemma wMatrix_displacement :
    HasDisplacement (wMatrix (K := F) p).entries 0 (p : ℤ) (p : ℤ) := by
  apply weightedShift_displacement
  intro j _
  simp [wShift]

lemma dzMatrix_displacement :
    HasDisplacement (dzMatrix (F := F) p).entries (-(p : ℤ)) (p : ℤ) (p : ℤ) := by
  apply weightedShift_displacement
  intro j _
  simp [zShift]

lemma dwMatrix_displacement (hp : 0 < p) :
    HasDisplacement (dwMatrix (F := F) p).entries (-(p : ℤ)) 0 0 := by
  apply weightedShift_displacement
  intro j hj
  have h : (p : ℤ) ≤ j.val.1 + j.val.2 := by
    by_contra h
    have hz := wDegree_zero_of_bottom p hp j h
    simp [hz] at hj
  simp [downShift, h]

lemma tMatrix_displacement (hp : 0 < p) :
    HasDisplacement (tMatrix (F := F) p).entries (-(p : ℤ)) 0 (p : ℤ) := by
  intro i j hij
  change dzMatrix p i j + dwMatrix p i j ≠ (0 : F) at hij
  by_cases hd : dzMatrix (F := F) p i j = 0
  · have hw : dwMatrix (F := F) p i j ≠ 0 := by simpa [hd] using hij
    obtain ⟨ha, hl, hu⟩ := dwMatrix_displacement (F := F) p hp i j hw
    constructor <;> omega
  · obtain ⟨ha, hl, hu⟩ := dzMatrix_displacement (F := F) p i j hd
    constructor <;> omega

/-- Exact first displacement and a second displacement interval for every source monomial. -/
theorem normalMonomialMatrix_displacement (hp : 0 < p) (i j : ℕ) (r : ℤ) :
    HasDisplacement (normalMonomialMatrix (F := F) p i j r).entries
      (r - p*i) (p*j-r) (p*(i+j)-r) := by
  have ht := displacement_pow (tMatrix (F := F) p) (tMatrix_displacement p hp) i
  have hw := displacement_pow (wMatrix (K := F) p) (wMatrix_displacement p) j
  have htw := displacement_product ((tMatrix (F := F) p)^i).entries
    ((wMatrix (K := F) p)^j).entries ht hw
  have h := displacement_product (((tMatrix (F := F) p)^i) * ((wMatrix p)^j)).entries
    (zMatrix (K := F) p r).entries htw (zMatrix_displacement p r)
  convert h using 1 <;> ring

/-- Fixed input and output leave only a finite window of Laurent and Taylor indices. -/
theorem finite_normalMonomial_sources (hp : 0 < p) (R : ℤ)
    (a b : Index (InLattice p)) :
    {q : (ℕ × ℕ) × ℤ | q.2 ≤ R ∧
      normalMonomialMatrix (F := F) p q.1.1 q.1.2 q.2 a b ≠ 0}.Finite := by
  let da := a.val.1 - b.val.1
  let dc := a.val.2 - b.val.2
  have hfinite : ((Set.Icc (0 : ℕ) (R-da).toNat ×ˢ Set.Icc (0 : ℕ) (R+dc).toNat) ×ˢ
      Set.Icc da R).Finite :=
    ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).prod (Set.finite_Icc _ _)
  apply hfinite.subset
  rintro ⟨⟨i,j⟩,r⟩ ⟨hr, hab⟩
  obtain ⟨ha, hl, hu⟩ := normalMonomialMatrix_displacement (F := F) p hp i j r a b hab
  have hpi : (i : ℤ) ≤ (p : ℤ) * i := by nlinarith
  have hpj : (j : ℤ) ≤ (p : ℤ) * j := by nlinarith
  change ((0 ≤ i ∧ i ≤ (R-da).toNat) ∧ (0 ≤ j ∧ j ≤ (R+dc).toNat)) ∧ da ≤ r ∧ r ≤ R
  dsimp [da,dc] at *
  constructor
  · constructor <;> constructor <;> omega
  · constructor <;> omega

/-- All intermediate indices and source monomial pairs contributing to a fixed
product entry form a finite set. This justifies rearranging the three sums in
the multiplicativity proof, even when the Taylor series are infinite. -/
theorem finite_normalMonomial_product_sources (hp : 0 < p) (R S : ℤ)
    (a b : Index (InLattice p)) :
    {q : Index (InLattice p) × (((ℕ × ℕ) × ℤ) × ((ℕ × ℕ) × ℤ)) |
      q.2.1.2 ≤ R ∧ q.2.2.2 ≤ S ∧
      normalMonomialMatrix (F := F) p q.2.1.1.1 q.2.1.1.2 q.2.1.2 a q.1 ≠ 0 ∧
      normalMonomialMatrix (F := F) p q.2.2.1.1 q.2.2.1.2 q.2.2.2 q.1 b ≠ 0}.Finite := by
  classical
  let J : Set (Index (InLattice p)) :=
    {k | a.val.1 - R ≤ k.val.1 ∧ k.val.1 ≤ b.val.1 + S ∧
      b.val.2 - S ≤ k.val.2 ∧ k.val.2 ≤ a.val.2 + R}
  have hJ : J.Finite := finite_rectangle _ _ _ _
  have hfinite := hJ.biUnion (fun k _ ↦
    (Set.finite_singleton k).prod
      ((finite_normalMonomial_sources (F := F) p hp R a k).prod
        (finite_normalMonomial_sources (F := F) p hp S k b)))
  apply hfinite.subset
  rintro ⟨k, ⟨⟨⟨i, j⟩, r⟩, ⟨⟨u, v⟩, s⟩⟩⟩ ⟨hr, hs, hleft, hright⟩
  change r ≤ R at hr
  change s ≤ S at hs
  have hk : k ∈ J := by
    obtain ⟨ha, hc⟩ := normalMonomialMatrix_bound (F := F) p i j r a k hleft
    obtain ⟨hb, hd⟩ := normalMonomialMatrix_bound (F := F) p u v s k b hright
    dsimp [J]
    omega
  exact Set.mem_iUnion₂.mpr ⟨k, hk, ⟨Set.mem_singleton k, ⟨hr, hleft⟩, ⟨hs, hright⟩⟩⟩

end MakarLimanov.Lattice
