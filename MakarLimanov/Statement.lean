import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact target and the final analytic reduction

The target is the original infimum over positive matrix sizes. `minRank` is an attained
minimum, not an arbitrarily chosen rank. This file does NOT prove `OriginalConjecture`.
-/

namespace MakarLimanov

universe u
variable {K : Type u} [Field K] {d : ℕ}

abbrev Mat (K : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) K
abbrev FreePoly (K : Type u) [Field K] (d : ℕ) := FreeAlgebra K (Fin d)

/-- Ordered, unital evaluation of a free polynomial on a matrix tuple. -/
noncomputable def eval (f : FreePoly K d) {n : ℕ} (Z : Fin d → Mat K n) : Mat K n :=
  FreeAlgebra.lift K Z f

/-- Evaluation uses matrix multiplication in the original order. -/
theorem eval_mul (f g : FreePoly K d) {n : ℕ} (Z : Fin d → Mat K n) :
    eval (f * g) Z = eval f Z * eval g Z :=
  map_mul (FreeAlgebra.lift K Z) f g

theorem eval_generator {n : ℕ} (Z : Fin d → Mat K n) (i : Fin d) :
    eval (FreeAlgebra.ι K i) Z = Z i := FreeAlgebra.lift_ι_apply Z i

theorem eval_constant (c : K) {n : ℕ} (Z : Fin d → Mat K n) :
    eval (algebraMap K (FreePoly K d) c) Z = algebraMap K (Mat K n) c :=
  (FreeAlgebra.lift K Z).commutes c

private theorem rank_exists (f : FreePoly K d) (n : ℕ) :
    ∃ r : ℕ, ∃ Z : Fin d → Mat K n, (eval f Z).rank = r :=
  ⟨_, fun _ ↦ 0, rfl⟩

/-- The least rank achieved by a matrix value, including the harmless auxiliary size zero. -/
noncomputable def minRank (f : FreePoly K d) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (rank_exists f n)

theorem minRank_attained (f : FreePoly K d) (n : ℕ) :
    ∃ Z : Fin d → Mat K n, (eval f Z).rank = minRank f n := by
  classical
  exact Nat.find_spec (rank_exists f n)

theorem minRank_le (f : FreePoly K d) {n : ℕ} (Z : Fin d → Mat K n) :
    minRank f n ≤ (eval f Z).rank := by
  classical
  exact Nat.find_min' (rank_exists f n) ⟨Z, rfl⟩

theorem minRank_le_size (f : FreePoly K d) (n : ℕ) : minRank f n ≤ n :=
  (minRank_le f (fun _ ↦ 0)).trans (Matrix.rank_le_width _)

/-- The set of ratios in the problem, with size zero explicitly excluded. -/
def rankRatios (f : FreePoly K d) : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ r = (minRank f n : ℝ) / n}

def RankInfimumZero (f : FreePoly K d) : Prop := sInf (rankRatios f) = 0

def Nonconstant (f : FreePoly K d) : Prop :=
  ∀ c : K, f ≠ algebraMap K (FreePoly K d) c

/-- The original conjecture at a fixed field and number of free generators. UNPROVED. -/
def OriginalConjecture (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (d : ℕ) : Prop :=
  ∀ f : FreePoly K d, Nonconstant f → RankInfimumZero f

theorem rankRatios_nonempty (f : FreePoly K d) : (rankRatios f).Nonempty :=
  ⟨(minRank f 1 : ℝ) / 1, 1, by decide, by simp⟩

theorem rankRatios_nonneg (f : FreePoly K d) {r : ℝ} (hr : r ∈ rankRatios f) : 0 ≤ r := by
  obtain ⟨n, _, rfl⟩ := hr
  positivity

theorem rankRatios_bddBelow (f : FreePoly K d) : BddBelow (rankRatios f) :=
  ⟨0, fun _ hr ↦ rankRatios_nonneg f hr⟩

/-- Exact equivalence with epsilon-small evaluated matrices, without assuming the conjecture. -/
theorem rankInfimumZero_iff (f : FreePoly K d) :
    RankInfimumZero f ↔ ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, 0 < n ∧ ∃ Z : Fin d → Mat K n, ((eval f Z).rank : ℝ) / n < ε := by
  constructor
  · intro h ε hε
    have hlt : sInf (rankRatios f) < ε := by simpa [RankInfimumZero] using h ▸ hε
    obtain ⟨r, ⟨n, hn, rfl⟩, hr⟩ :=
      (csInf_lt_iff (rankRatios_bddBelow f) (rankRatios_nonempty f)).mp hlt
    obtain ⟨Z, hZ⟩ := minRank_attained f n
    exact ⟨n, hn, Z, by simpa [hZ] using hr⟩
  · intro h
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (rankRatios_nonempty f)
      (fun _ hr ↦ rankRatios_nonneg f hr)
    intro ε hε
    obtain ⟨n, hn, Z, hZ⟩ := h ε hε
    refine ⟨(minRank f n : ℝ) / n, ⟨n, hn, rfl⟩, lt_of_le_of_lt ?_ hZ⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast minRank_le f Z) (by positivity)

/-- The analytic last step, conditional on the substantive matrix witnesses. -/
theorem rankInfimumZero_of_quantitative_witnesses (f : FreePoly K d)
    (C : ℝ) (hC : 0 ≤ C)
    (witnesses : ∀ T : ℕ, 0 < T → ∃ n : ℕ, 0 < n ∧
      ∃ Z : Fin d → Mat K n, ((eval f Z).rank : ℝ) / n ≤ C / T) :
    RankInfimumZero f := by
  rw [rankInfimumZero_iff]
  intro ε hε
  obtain ⟨T, hT⟩ := exists_nat_gt (C / ε)
  have hTpos : 0 < (T : ℝ) := lt_of_le_of_lt (div_nonneg hC hε.le) hT
  have hTnat : 0 < T := by exact_mod_cast hTpos
  obtain ⟨n, hn, Z, hZ⟩ := witnesses T hTnat
  refine ⟨n, hn, Z, hZ.trans_lt ?_⟩
  apply (div_lt_iff₀ hTpos).mpr
  simpa [mul_comm] using (div_lt_iff₀ hε).mp hT

/-- Scalar evaluation followed by the scalar-matrix map is matrix evaluation. -/
theorem eval_scalar (f : FreePoly K d) (a : Fin d → K) (n : ℕ) :
    eval f (fun i ↦ algebraMap K (Mat K n) (a i)) =
      algebraMap K (Mat K n) (FreeAlgebra.lift K a f) := by
  have h : FreeAlgebra.lift K (fun i ↦ algebraMap K (Mat K n) (a i)) =
      (Algebra.ofId K (Mat K n)).comp (FreeAlgebra.lift K a) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  exact DFunLike.congr_fun h f

/-- The scalar-zero branch of the paper is fully verified. -/
theorem rankInfimumZero_of_scalar_zero (f : FreePoly K d) (a : Fin d → K)
    (ha : FreeAlgebra.lift K a f = 0) : RankInfimumZero f := by
  rw [rankInfimumZero_iff]
  intro ε hε
  refine ⟨1, by decide, fun i ↦ algebraMap K (Mat K 1) (a i), ?_⟩
  simpa [eval_scalar, ha] using hε

end MakarLimanov
