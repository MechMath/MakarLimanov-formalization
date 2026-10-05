import MakarLimanov.SymbolVariations

/-!
# Differential subalgebras of symbol coefficients

Star multiplication preserves a coefficient subalgebra stable under both derivations.
In particular, its infinite sums do not introduce inverses of differential indeterminates.
-/

namespace MakarLimanov.DifferentialCoefficients

open SymbolSeries SymbolSeries.StarSeries HahnSeries

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- All coefficients of a Laurent series belong to a specified subalgebra. -/
def CoefficientsIn (S : Subalgebra k F) (x : LaurentSeries F) : Prop :=
  ∀ n, x.coeff n ∈ S

variable {S : Subalgebra k F} {x y : LaurentSeries F}

theorem zero : CoefficientsIn S 0 := fun _ ↦ by simp

theorem single (n : ℤ) {a : F} (ha : a ∈ S) : CoefficientsIn S (HahnSeries.single n a) := by
  intro m
  by_cases hm : m = n <;> simp [hm, ha, S.zero_mem]

theorem add (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) :
    CoefficientsIn S (x + y) := fun n ↦ by simpa using S.add_mem (hx n) (hy n)

theorem mul (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) :
    CoefficientsIn S (x * y) := by
  intro n
  rw [coeff_mul]
  exact S.sum_mem (fun ij _ ↦ S.mul_mem (hx ij.1) (hy ij.2))

theorem smul {a : F} (ha : a ∈ S) (hx : CoefficientsIn S x) :
    CoefficientsIn S (a • x) := fun n ↦ by
  simpa only [coeff_smul, smul_eq_mul] using S.mul_mem ha (hx n)

theorem coefficientDerivation (d : Derivation k F F)
    (hd : ∀ a ∈ S, d a ∈ S) (hx : CoefficientsIn S x) :
    CoefficientsIn S (SymbolSeries.coefficientDerivation d x) := fun n ↦ hd _ (hx n)

theorem deltaOperator (p : ℕ) (η : Derivation k F F)
    (hη : ∀ a ∈ S, η a ∈ S) (hx : CoefficientsIn S x) :
    CoefficientsIn S (SymbolSeries.deltaOperator p η x) := by
  intro n
  rw [deltaOperator_coeff]
  have hp : (p : F)⁻¹ ∈ S := by
    simpa only [map_inv₀, map_natCast] using S.algebraMap_mem ((p : k)⁻¹)
  exact S.sub_mem (hη _ (hx _)) (S.mul_mem (S.mul_mem hp (S.intCast_mem _)) (hx _))

theorem iterate {T : LaurentSeries F → LaurentSeries F}
    (hT : ∀ x, CoefficientsIn S x → CoefficientsIn S (T x))
    (hx : CoefficientsIn S x) (j : ℕ) : CoefficientsIn S (T^[j] x) := by
  induction j with
  | zero => exact hx
  | succ j ih => simpa only [Function.iterate_succ_apply'] using hT _ ih

theorem starTerm (p : ℕ) (δ η : Derivation k F F)
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) (j : ℕ) :
    CoefficientsIn S (SymbolSeries.starTerm p δ η x y j) := by
  apply smul
  · simpa only [map_inv₀, map_natCast] using S.algebraMap_mem ((j.factorial : k)⁻¹)
  · exact mul (iterate (fun _ hx ↦ deltaOperator p η hη hx) hx j)
      (iterate (fun _ hy ↦ coefficientDerivation δ hδ hy) hy j)

/-- Each infinite star-product coefficient is a finite sum inside the coefficient subalgebra. -/
theorem starProduct (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (hx : CoefficientsIn S x) (hy : CoefficientsIn S y) :
    CoefficientsIn S (SymbolSeries.starProduct p hp δ η x y) := by
  intro n
  rw [starProduct_coeff_finite]
  exact S.sum_mem (fun j _ ↦ starTerm p δ η hδ hη hx hy j n)

variable [CharZero F]

/-- Ordered free-polynomial evaluation never leaves the differential coefficient subalgebra. -/
theorem evaluate {ι : Type*} (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (X : ι → StarSeries p hp δ η hc) (hX : ∀ i, CoefficientsIn S (toSeries (X i)))
    (f : FreeAlgebra k ι) : CoefficientsIn S (toSeries (FreeAlgebra.lift k X f)) := by
  induction f with
  | grade0 a =>
    simpa using single 0 (S.algebraMap_mem a)
  | grade1 i => simpa using hX i
  | add f g hf hg => simpa using add hf hg
  | mul f g hf hg => simpa using starProduct p hp δ η hδ hη hf hg

/-- Every variation coefficient has coefficients in the same differential subalgebra. -/
theorem variation (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (hδ : ∀ a ∈ S, δ a ∈ S) (hη : ∀ a ∈ S, η a ∈ S)
    (x z v : StarSeries p hp δ η hc)
    (hx : CoefficientsIn S (toSeries x)) (hz : CoefficientsIn S (toSeries z))
    (hv : CoefficientsIn S (toSeries v)) (f : FreeAlgebra k Bool) (n : ℕ) :
    CoefficientsIn S (toSeries (Variations.variation f x z v n)) := by
  induction f generalizing n with
  | grade0 a =>
    intro m
    by_cases hn : n = 0
    · subst n
      simpa [Variations.variation, Variations.expansion] using single 0 (S.algebraMap_mem a) m
    · simp [Variations.variation, Variations.expansion, Polynomial.coeff_C, hn]
  | grade1 b =>
    cases b
    · intro m
      by_cases hn : n = 0
      · subst n
        simpa [Variations.variation] using hx m
      · simp [Variations.variation, Polynomial.coeff_C, hn]
    · intro m
      by_cases hn : n = 0
      · subst n
        simpa [Variations.variation] using hz m
      · by_cases hn₁ : n = 1
        · subst n
          simpa [Variations.variation] using hv m
        · simp [Variations.variation, Polynomial.coeff_C, Polynomial.coeff_X,
            hn, Ne.symm hn₁]
  | add f g hf hg => simpa using add (hf n) (hg n)
  | mul f g hf hg =>
    intro m
    rw [Variations.variation_mul]
    change (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      SymbolSeries.starProduct p hp δ η (toSeries (Variations.variation f x z v ij.1))
        (toSeries (Variations.variation g x z v ij.2))).coeff m ∈ S
    simp only [coeff_sum]
    exact S.sum_mem (fun ij _ ↦ starProduct p hp δ η hδ hη (hf ij.1) (hg ij.2) m)

end

end MakarLimanov.DifferentialCoefficients
