import MakarLimanov.Numerics

/-!
# The complete inequalities at the next supporting slope

The maximal slope places all positive variations above the new residual
order. Every degree attaining that order is at most the old multiplicity,
which bounds the full leading polynomial at the next stage.
-/

namespace MakarLimanov.SupportingSlope

/-- Besides a supporting index, retain the order bounds and the degree bound
for every active index attaining the new supporting line. -/
theorem exists_supporting_line
    (ρ ρ' s : ℚ) (a : ℕ → ℚ) (active : Finset ℕ)
    {m : ℕ} (hm : 0 < m) (hmem : m ∈ active)
    (hρ : ρ < ρ') (ha : ∀ j ∈ active, ρ ≤ a j) (ham : a m = ρ)
    (hpositive : ∀ j ∈ active, 0 < j) :
    ∃ (s' : ℚ) (k : ℕ), k ∈ active ∧ 0 < k ∧ k ≤ m ∧ s < s' ∧
      a k + (k : ℚ) * (s' - s) = ρ' ∧
      (∀ j ∈ active, ρ' ≤ a j + (j : ℚ) * (s' - s)) ∧
      (∀ j ∈ active, a j + (j : ℚ) * (s' - s) = ρ' → j ≤ m) := by
  obtain ⟨k, hk, hkpos, hkm, himprove, hmax⟩ :=
    MakarLimanov.exists_next_slope ρ ρ' s a active hm hmem hρ ha ham
  let s' := s + (ρ' - a k) / (k : ℚ)
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hkpos
  have hbounds : ∀ j ∈ active, ρ' ≤ a j + (j : ℚ) * (s' - s) := by
    intro j hj
    have hjQ : (0 : ℚ) < j := by exact_mod_cast hpositive j hj
    have hdiv : (ρ' - a j) / (j : ℚ) ≤ s' - s := by
      have h := hmax j hj
      dsimp [s']
      linarith
    have hmul := (div_le_iff₀ hjQ).mp hdiv
    nlinarith
  refine ⟨s', k, hk, hkpos, hkm, himprove, ?_, hbounds, ?_⟩
  · dsimp [s']
    field_simp
    <;> ring
  · intro j hj heq
    by_contra hjm
    have hjQ : (0 : ℚ) < j := by exact_mod_cast hpositive j hj
    have heqdiv : s' = s + (ρ' - a j) / (j : ℚ) := by
      dsimp [s'] at heq ⊢
      have hratio : s' - s = (ρ' - a j) / (j : ℚ) := by
        apply (eq_div_iff (ne_of_gt hjQ)).2
        nlinarith
      calc
        s' = s + (s' - s) := by ring
        _ = s + (ρ' - a j) / (j : ℚ) := by rw [hratio]
    have hbad := MakarLimanov.next_slope_degree_bound ρ ρ' (a j) s
      (m := m) (k := j) hm (by omega) (ha j hj) hρ
    have hmm := hmax m hmem
    rw [ham] at hmm
    change s + (ρ' - ρ) / (m : ℚ) ≤ s' at hmm
    rw [heqdiv] at hmm
    exact (not_lt_of_ge hmm) hbad

end MakarLimanov.SupportingSlope
