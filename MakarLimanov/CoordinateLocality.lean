import MakarLimanov.RealizationTruncation

/-!
# Finite coefficient dependencies of the coordinate operations

Coordinate differentiation reads finitely many source coefficients. Laurent
multiplication has a uniform finite coefficient window once both input lower
bounds are fixed.
-/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates HahnSeries

variable {F : Type*} [Field F]

/-- The outer coordinate derivative reads exactly the next outer Taylor coefficient. -/
lemma sourceCoeff_coordinateT (x : LaurentSeries (BiSeries F)) (i j : ℕ) (r : ℤ) :
    sourceCoeff (coordinateT x) ((i, j), r) =
      sourceCoeff x ((i + 1, j), r) * (i + 1 : ℕ) := by
  simp only [sourceCoeff, coordinateT_coeff, coeff_partialT]
  rw [← Nat.cast_add_one, ← nsmul_eq_mul']
  rw [map_nsmul]
  simp [nsmul_eq_mul, mul_comm]

/-- The shifted coordinate derivative reads two adjacent inner Taylor coefficients. -/
lemma sourceCoeff_coordinateDelta (p : ℕ) (x : LaurentSeries (BiSeries F))
    (i j : ℕ) (r : ℤ) :
    sourceCoeff (coordinateDelta p x) ((i, j), r) =
      sourceCoeff x ((i, j + 1), r + p) * (j + 1 : ℕ) +
        ((r + p : ℤ) : F) / (p : F) * sourceCoeff x ((i, j), r + p) := by
  simp only [sourceCoeff, coordinateDelta_coeff]
  have he : -r - (p : ℤ) = -(r + p) := by ring
  rw [he]
  have hr : ((r + p : ℤ) : BiSeries F) =
      PowerSeries.C (PowerSeries.C ((r + p : ℤ) : F)) := by simp
  rw [Int.cast_neg, hr, mul_neg, neg_mul, sub_neg_eq_add, ← map_mul]
  simp only [map_add, coeff_partialW, PowerSeries.coeff_derivative,
    PowerSeries.coeff_C_mul]
  simp only [← map_mul, PowerSeries.coeff_C_mul]
  simp only [Int.cast_add, Int.cast_natCast, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
  ring

end MakarLimanov.MatrixRealization



namespace MakarLimanov.TaylorCoordinates

open HahnSeries Finset

variable {F : Type*} [Field F]

/-- The Laurent convolution window depends only on the two lower support bounds. -/
lemma coeff_mul_Icc {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) (n : ℤ) :
    (x * y).coeff n = ∑ m ∈ Finset.Icc b (n - c), x.coeff m * y.coeff (n - m) := by
  classical
  let e : ℤ ↪ ℤ × ℤ := ⟨fun m ↦ (m, n - m), fun _ _ h ↦ (Prod.mk.inj h).1⟩
  have hs : addAntidiagonal x.isPWO_support y.isPWO_support n ⊆
      (Finset.Icc b (n - c)).map e := by
    intro ij hij
    obtain ⟨hi, hj, he⟩ := mem_addAntidiagonal.mp hij
    have hb : b ≤ ij.1 := by
      by_contra! h
      exact hi (hx _ h)
    have hc : c ≤ ij.2 := by
      by_contra! h
      exact hj (hy _ h)
    apply Finset.mem_map.mpr
    refine ⟨ij.1, Finset.mem_Icc.mpr ⟨hb, by omega⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp [e]
      omega
  rw [coeff_mul]
  symm
  change (∑ m ∈ Finset.Icc b (n - c), (fun ij : ℤ × ℤ ↦
    x.coeff ij.1 * y.coeff ij.2) (e m)) = _
  rw [← Finset.sum_map (f := fun ij : ℤ × ℤ ↦ x.coeff ij.1 * y.coeff ij.2)]
  symm
  apply Finset.sum_subset hs
  intro ij hij hnot
  obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hij
  by_cases hx0 : x.coeff m = 0
  · simp [e, hx0]
  · by_cases hy0 : y.coeff (n - m) = 0
    · simp [e, hy0]
    · exact False.elim (hnot (mem_addAntidiagonal.mpr ⟨hx0, hy0, by dsimp [e]; omega⟩))

end MakarLimanov.TaylorCoordinates

namespace MakarLimanov.MatrixRealization

open TaylorCoordinates

variable {F : Type*} [Field F]

/-- The finite source dependency tree of an iterated shifted derivative. -/
def deltaSources (p : ℕ) : ℕ → Source → Finset Source
  | 0, q => {q}
  | n + 1, q =>
      deltaSources p n ((q.1.1, q.1.2 + 1), q.2 + p) ∪
        deltaSources p n ((q.1.1, q.1.2), q.2 + p)

/-- Matching the dependency tree suffices to match an iterated `Δ` coefficient. -/
theorem sourceCoeff_delta_iterate_eq (p n : ℕ) (q : Source)
    (x y : LaurentSeries (BiSeries F))
    (h : ∀ t ∈ deltaSources p n q, sourceCoeff x t = sourceCoeff y t) :
    sourceCoeff ((coordinateDelta p)^[n] x) q =
      sourceCoeff ((coordinateDelta p)^[n] y) q := by
  induction n generalizing q with
  | zero => exact h q (by simp [deltaSources])
  | succ n ih =>
    rcases q with ⟨⟨i, j⟩, r⟩
    simp only [Function.iterate_succ_apply', sourceCoeff_coordinateDelta]
    rw [ih ((i, j + 1), r + p) (fun t ht ↦ h t
      (Finset.mem_union_left _ ht))]
    rw [ih ((i, j), r + p) (fun t ht ↦ h t
      (Finset.mem_union_right _ ht))]

/-- Matching one shifted source coefficient suffices for iterated `t` differentiation. -/
theorem sourceCoeff_T_iterate_eq (n i j : ℕ) (r : ℤ)
    (x y : LaurentSeries (BiSeries F))
    (h : sourceCoeff x ((i + n, j), r) = sourceCoeff y ((i + n, j), r)) :
    sourceCoeff (coordinateT^[n] x) ((i, j), r) =
      sourceCoeff (coordinateT^[n] y) ((i, j), r) := by
  induction n generalizing i with
  | zero => simpa using h
  | succ n ih =>
    simp only [Function.iterate_succ_apply', sourceCoeff_coordinateT]
    rw [ih (i + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)]

end MakarLimanov.MatrixRealization


namespace MakarLimanov.MatrixRealization

open TaylorCoordinates HahnSeries Finset

variable {F : Type*} [Field F]

/-- A specified product source coefficient is a finite triple convolution. -/
lemma sourceCoeff_mul_Icc {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) (i j : ℕ) (r : ℤ) :
    sourceCoeff (x * y) ((i, j), r) =
      ∑ m ∈ Finset.Icc b (-r - c), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal i,
        ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal j,
          sourceCoeff x ((ab.1, uv.1), -m) * sourceCoeff y ((ab.2, uv.2), r + m) := by
  simp only [sourceCoeff, coeff_mul_Icc hx hy, map_sum, PowerSeries.coeff_mul,
    neg_neg]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro ab hab
  apply Finset.sum_congr rfl
  intro uv huv
  rw [show -(r + m) = -r - m by ring]

/-- With fixed lower Laurent bounds, a product coefficient depends on finite
sets of source coefficients of both inputs. The sets are uniform over all
inputs satisfying those bounds. -/
theorem exists_mul_coefficient_window (b c : ℤ) (q : Source) :
    ∃ s t : Finset Source, ∀ x y x' y' : LaurentSeries (BiSeries F),
      CoordinateBound b x → CoordinateBound c y →
      CoordinateBound b x' → CoordinateBound c y' →
      (∀ u ∈ s, sourceCoeff x u = sourceCoeff x' u) →
      (∀ u ∈ t, sourceCoeff y u = sourceCoeff y' u) →
      sourceCoeff (x * y) q = sourceCoeff (x' * y') q := by
  classical
  rcases q with ⟨⟨i, j⟩, r⟩
  let K := (Finset.Icc b (-r - c)) ×ˢ
    ((Finset.HasAntidiagonal.antidiagonal i) ×ˢ (Finset.HasAntidiagonal.antidiagonal j))
  let s := K.image (fun z ↦ ((z.2.1.1, z.2.2.1), -z.1))
  let t := K.image (fun z ↦ ((z.2.1.2, z.2.2.2), r + z.1))
  refine ⟨s, t, ?_⟩
  intro x y x' y' hx hy hx' hy' hs ht
  rw [sourceCoeff_mul_Icc hx hy, sourceCoeff_mul_Icc hx' hy']
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro ab hab
  apply Finset.sum_congr rfl
  intro uv huv
  have hK : (m, ab, uv) ∈ K :=
    Finset.mem_product.mpr ⟨hm, Finset.mem_product.mpr ⟨hab, huv⟩⟩
  rw [hs _ (Finset.mem_image_of_mem _ hK), ht _ (Finset.mem_image_of_mem _ hK)]

/-- A diamond summand has uniform finite source dependencies under fixed
lower Laurent bounds, including all of its iterated derivatives. -/
theorem exists_diamondTerm_coefficient_window (p n : ℕ) (b c : ℤ) (q : Source) :
    ∃ s t : Finset Source, ∀ x y x' y' : LaurentSeries (BiSeries F),
      CoordinateBound b x → CoordinateBound c y →
      CoordinateBound b x' → CoordinateBound c y' →
      (∀ u ∈ s, sourceCoeff x u = sourceCoeff x' u) →
      (∀ u ∈ t, sourceCoeff y u = sourceCoeff y' u) →
      sourceCoeff (diamondTerm p x y n) q = sourceCoeff (diamondTerm p x' y' n) q := by
  classical
  obtain ⟨s₀, t₀, hw⟩ := exists_mul_coefficient_window (F := F) (b + p * n) c q
  let s := s₀.biUnion (deltaSources p n)
  let t := t₀.image (fun u ↦ ((u.1.1 + n, u.1.2), u.2))
  refine ⟨s, t, ?_⟩
  intro x y x' y' hx hy hx' hy' hs ht
  have he := hw ((coordinateDelta p)^[n] x) (coordinateT^[n] y)
    ((coordinateDelta p)^[n] x') (coordinateT^[n] y')
    (hx.coordinateDelta_iterate p n) (hy.coordinateT_iterate n)
    (hx'.coordinateDelta_iterate p n) (hy'.coordinateT_iterate n)
    (fun u hu ↦ sourceCoeff_delta_iterate_eq p n u x x' (fun v hv ↦
      hs v (Finset.mem_biUnion.mpr ⟨u, hu, hv⟩)))
    (fun u hu ↦ sourceCoeff_T_iterate_eq n u.1.1 u.1.2 u.2 y y'
      (ht _ (Finset.mem_image_of_mem _ hu)))
  simp only [diamondTerm, coordinateConstant_mul, sourceCoeff_smul]
  rw [he]

end MakarLimanov.MatrixRealization
