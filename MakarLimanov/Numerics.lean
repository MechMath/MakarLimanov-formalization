import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Numerical obligations used by finite approximation and compression

These theorems check arithmetic implications. Their hypotheses are explicit; they do not
construct Newton corrections, symbols, commuting derivations, or matrix witnesses.
-/

namespace MakarLimanov

/-- The denominator-times-multiplicity budget is preserved by the orbit estimate. -/
theorem newton_budget {p e m q b M : ℕ}
    (horbit : e * m ≤ q) (hq : q ≤ b) (hbudget : p * b ≤ M) :
    (p * e) * m ≤ M := by
  calc
    (p * e) * m = p * (e * m) := Nat.mul_assoc _ _ _
    _ ≤ p * q := Nat.mul_le_mul_left p horbit
    _ ≤ p * b := Nat.mul_le_mul_left p hq
    _ ≤ M := hbudget

/-- Positive multiplicity turns the budget into a bound on the denominator. -/
theorem denominator_bound {p m M : ℕ} (hm : 0 < m) (h : p * m ≤ M) : p ≤ M := by
  nlinarith

/-- Uniform progress bounds the number of residual improvements needed for precision T. -/
theorem finite_progress {M T : ℕ} (hM : 0 < M) (ρ : ℕ → ℚ)
    (hzero : 0 ≤ ρ 0)
    (hstep : ∀ j < M * T, ρ j + 1 / (M : ℚ) ≤ ρ (j + 1)) :
    (T : ℚ) ≤ ρ (M * T) := by
  have hpos : (0 : ℚ) < M := by exact_mod_cast hM
  have hbound : ∀ j ≤ M * T, (j : ℚ) / M ≤ ρ j := by
    intro j
    induction j with
    | zero => simpa using hzero
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hs := hstep j (by omega)
      push_cast
      rw [add_div]
      linarith
  have h := hbound (M * T) le_rfl
  simpa [Nat.cast_mul, ne_of_gt hpos] using h

/-- The numerical Newton schedule has a certified stopping index bounded by `M*T`.
The endpoint is allowed as a stopping stage, which also covers an exactly vanishing
residual represented by arbitrarily large precision. -/
theorem exists_bounded_precision_stage {M T : ℕ} (hM : 0 < M)
    (ρ : ℕ → ℚ) (hzero : 0 ≤ ρ 0)
    (hstep : ∀ j < M * T, ρ j + 1 / (M : ℚ) ≤ ρ (j + 1)) :
    ∃ J ≤ M * T, (T : ℚ) ≤ ρ J := by
  refine ⟨M * T, le_rfl, ?_⟩
  exact finite_progress hM ρ hzero hstep

/-- The initial active coefficient with denominator at most `M` gives the
initial slope bound used in the finite Newton proposition. -/
theorem initial_slope_bound {A M : ℕ} {ρ r : ℤ} {k : ℕ}
    (hM : 0 < M) (hk : 0 < k) (hkM : k ≤ M)
    (hr : r ≤ (A * k : ℕ) - 1) (hρ : 0 ≤ ρ) :
    (-A : ℚ) + 1 / (M : ℚ) ≤ ((ρ - r : ℤ) : ℚ) / k := by
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hkM' : (k : ℚ) ≤ M := by exact_mod_cast hkM
  have hr' : (r : ℚ) ≤ A * k - 1 := by
    exact_mod_cast hr
  have hρ' : (0 : ℚ) ≤ ρ := by exact_mod_cast hρ
  have hstep : (0 : ℚ) < 1 / k := by positivity
  have hmain : (-A : ℚ) + 1 / k ≤ ((ρ - r : ℤ) : ℚ) / k := by
    calc
      (-A : ℚ) + 1 / k = (-A * k + 1) / k := by field_simp
      _ ≤ ((ρ - r : ℤ) : ℚ) / k := by
        apply (div_le_div_iff₀ hkQ hkQ).mpr
        push_cast
        nlinarith
  have hunit : 1 / (M : ℚ) ≤ 1 / k := by
    exact (div_le_div_iff₀ hMQ hkQ).mpr (by simpa using hkM')
  linarith

/-- Larger-degree terms cannot control the next slope after a multiplicity-m correction. -/
theorem next_slope_degree_bound (ρ ρ' a s : ℚ) {m k : ℕ}
    (hm : 0 < m) (hkm : m < k) (ha : ρ ≤ a) (hρ : ρ < ρ') :
    s + (ρ' - a) / (k : ℚ) < s + (ρ' - ρ) / (m : ℚ) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hk' : (0 : ℚ) < k := by exact_mod_cast (lt_trans hm hkm)
  have hmk : (m : ℚ) < k := by exact_mod_cast hkm
  apply add_lt_add_right
  apply (div_lt_div_iff₀ hk' hm').mpr
  nlinarith

set_option maxHeartbeats 800000 in
/-- Strict improvement on a refined lattice supplies the uniform termination increment. -/
theorem newton_lattice_progress {r r' : ℤ} {p e M : ℕ}
    (hp : 0 < p) (he : 0 < e) (hbudget : p * e ≤ M)
    (hr : r * (e : ℤ) < r') :
    (r : ℚ) / p + 1 / (M : ℚ) ≤ (r' : ℚ) / (p * e : ℕ) := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have heQ : (0 : ℚ) < e := by exact_mod_cast he
  have hpe : 0 < p * e := Nat.mul_pos hp he
  have hM : 0 < M := lt_of_lt_of_le hpe hbudget
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hpeQ : (0 : ℚ) < (p * e : ℕ) := by exact_mod_cast hpe
  have hB : (p * e : ℕ) ≤ (M : ℚ) := by exact_mod_cast hbudget
  have hrQ : (r : ℚ) * e + 1 ≤ r' := by
    exact_mod_cast (show r * (e : ℤ) + 1 ≤ r' by omega)
  have hunit : 1 / (M : ℚ) ≤ 1 / (p * e : ℕ) := by
    apply (div_le_div_iff₀ hMQ hpeQ).mpr
    simpa using hB
  calc
    (r : ℚ) / p + 1 / (M : ℚ) ≤ (r : ℚ) / p + 1 / (p * e : ℕ) :=
      add_le_add_right hunit _
    _ = ((r : ℚ) * e + 1) / (p * e : ℕ) := by
      push_cast
      field_simp
    _ ≤ (r' : ℚ) / (p * e : ℕ) :=
      (div_le_div_iff_of_pos_right hpeQ).mpr hrQ

/-- A maximal next slope exists, improves the old one, and has degree at most `m`. -/
theorem exists_next_slope (ρ ρ' s : ℚ) (a : ℕ → ℚ) (active : Finset ℕ)
    {m : ℕ} (hm : 0 < m) (hmem : m ∈ active)
    (hρ : ρ < ρ') (ha : ∀ k ∈ active, ρ ≤ a k) (ham : a m = ρ) :
    ∃ k ∈ active, 0 < k ∧ k ≤ m ∧ s < s + (ρ' - a k) / (k : ℚ) ∧
      ∀ j ∈ active, s + (ρ' - a j) / (j : ℚ) ≤
        s + (ρ' - a k) / (k : ℚ) := by
  obtain ⟨k, hk, hmax⟩ := active.exists_max_image
    (fun j ↦ s + (ρ' - a j) / (j : ℚ)) ⟨m, hmem⟩
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have himprove : s < s + (ρ' - a m) / (m : ℚ) := by
    rw [ham]
    have : 0 < (ρ' - ρ) / (m : ℚ) := div_pos (sub_pos.mpr hρ) hmQ
    linarith
  have hkm : k ≤ m := by
    by_contra hn
    have hbad := next_slope_degree_bound ρ ρ' (a k) s (m := m) (k := k)
      hm (by omega) (ha k hk) hρ
    rw [← ham] at hbad
    exact (not_lt_of_ge (hmax m hmem)) hbad
  have hbetter := lt_of_lt_of_le himprove (hmax m hmem)
  have hkpos : 0 < k := by
    by_contra hn
    have hkzero : k = 0 := by omega
    simp [hkzero] at hbetter
  exact ⟨k, hk, hkpos, hkm, hbetter, hmax⟩

/-- The p-dependent dimension and rank bound give a p-independent normalized estimate. -/
theorem compressed_ratio_bound {D A p T q : ℕ} (hp : 0 < p) (hT : 0 < T)
    (hq : q ≤ 4 * D * A * p * T) :
    (q : ℝ) / ((p : ℝ) * T ^ 2) ≤ 4 * D * A / (T : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  calc
    (q : ℝ) / ((p : ℝ) * T ^ 2) ≤
        (4 * D * A * p * T : ℝ) / ((p : ℝ) * T ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hq
    _ = 4 * D * A / (T : ℝ) := by
      field_simp

end MakarLimanov
