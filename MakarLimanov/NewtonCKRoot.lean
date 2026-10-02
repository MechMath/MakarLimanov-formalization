import MakarLimanov.NewtonRoot

/-!
# Realizing a triangular jet equation in the Cauchy--Kowalevski strip

The highest jet `(N, 0)` is the algebraic leader. Every other jet in the triangle
`a + b ≤ N` embeds in the free strip `a < N`. The strip derivations therefore
turn the generic algebraic point into the actual mixed jets of one element.
-/

namespace MakarLimanov.NewtonCKRoot

open MvPolynomial GenericKernel NewtonRoot

noncomputable section

/-- The mixed jets of total differential order at most `N`. -/
abbrev Triangle (N : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 ≤ N}

/-- The pure top derivative, used as the algebraic leader. -/
def leader (N : ℕ) : Triangle N := ⟨(N, 0), by simp⟩

/-- Every triangular jet except the leader belongs to the free strip. -/
def stripIndex {N : ℕ} (ij : Triangle N) : Option (Fin N × ℕ) :=
  if ha : ij.val.1 < N then some (⟨ij.val.1, ha⟩, ij.val.2) else none

theorem eq_leader_of_not_lt {N : ℕ} (ij : Triangle N) (ha : ¬ ij.val.1 < N) :
    ij = leader N := by
  apply Subtype.ext
  have h := ij.property
  apply Prod.ext <;> dsimp [leader] <;> omega

@[simp] theorem stripIndex_leader (N : ℕ) : stripIndex (leader N) = none := by
  simp [stripIndex, leader]

theorem stripIndex_injective {N : ℕ} : Function.Injective (stripIndex (N := N)) := by
  intro ij kl h
  by_cases hi : ij.val.1 < N
  · by_cases hk : kl.val.1 < N
    · simp only [stripIndex, dif_pos hi, dif_pos hk, Option.some.injEq] at h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x : Fin N × ℕ ↦ x.1.val) h
      · exact congrArg (fun x : Fin N × ℕ ↦ x.2) h
    · simp [stripIndex, hi, hk] at h
  · by_cases hk : kl.val.1 < N
    · simp [stripIndex, hi, hk] at h
    · exact (eq_leader_of_not_lt ij hi).trans (eq_leader_of_not_lt kl hk).symm

universe u

variable {k F : Type u} [CommRing k] [Field F] [CharZero F] [Algebra k F]
  {N : ℕ}

/-- Encode a triangular jet equation as a univariate equation over the free strip ring. -/
def stripPolynomial (P : MvPolynomial (Triangle N) F) :
    Polynomial (MvPolynomial (Fin N × ℕ) F) :=
  optionEquivLeft F (Fin N × ℕ) (rename stripIndex P)

omit [CharZero F] in
theorem irreducible_stripPolynomial {P : MvPolynomial (Triangle N) F}
    (hP : Irreducible P) : Irreducible (stripPolynomial P) :=
  (irreducible_rename stripIndex stripIndex_injective hP).map (optionEquivLeft F _)

omit [CharZero F] in
/-- Splitting the leader and adjoining the extra strip variables preserve divisibility. -/
theorem stripPolynomial_dvd_iff (P Q : MvPolynomial (Triangle N) F) :
    stripPolynomial P ∣ stripPolynomial Q ↔ P ∣ Q := by
  rw [stripPolynomial, stripPolynomial, map_dvd_iff]
  exact rename_dvd_iff stripIndex stripIndex_injective P Q

omit [CharZero F] in
/-- The pure leader derivative becomes the ordinary derivative after strip encoding. -/
theorem stripPolynomial_leader_pderiv (P : MvPolynomial (Triangle N) F) :
    stripPolynomial (pderiv (leader N) P) = (stripPolynomial P).derivative := by
  unfold stripPolynomial
  rw [← optionEquivLeft_pderiv_none]
  have hrename := pderiv_rename (f := stripIndex) stripIndex_injective (leader N) P
  simpa only [stripIndex_leader] using
    (congrArg (optionEquivLeft F (Fin N × ℕ)) hrename).symm

omit [CharZero F] in
/-- A polynomial and its renamed version evaluate identically on corresponding jets. -/
theorem aeval_strip_rename {E : Type*} [CommRing E] [Algebra F E]
    (point : Option (Fin N × ℕ) → E) (jets : Triangle N → E)
    (hpoint : ∀ ij, point (stripIndex ij) = jets ij) (P : MvPolynomial (Triangle N) F) :
    MvPolynomial.aeval point (rename stripIndex P) = MvPolynomial.aeval jets P := by
  rw [MvPolynomial.aeval_rename]
  have he : point ∘ stripIndex = jets := funext hpoint
  rw [he]

/--
An irreducible triangular jet equation with a positive-degree pure leader has an
actual solution in a commuting differential extension. Every polynomial outside
its principal ideal remains nonzero on those same mixed jets.
-/
theorem exists_differential_factor_root (P : MvPolynomial (Triangle N) F)
    (hP : Irreducible P) (hdeg : (stripPolynomial P).natDegree ≠ 0)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) (hN : 0 < N) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra F E)
      (_ : IsScalarTower k F E), ∃ (D H : Derivation k E E) (v : E),
      Function.Commute D H ∧
      (∀ a : F, D (algebraMap F E a) = algebraMap F E (δ a)) ∧
      (∀ a : F, H (algebraMap F E a) = algebraMap F E (η a)) ∧
      MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v)) P = 0 ∧
      MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v))
          (pderiv (leader N) P) ≠ 0 ∧
      (∀ Q : MvPolynomial (Triangle N) F,
        MvPolynomial.aeval (fun ij : Triangle N ↦ D^[ij.val.1] (H^[ij.val.2] v)) Q = 0
          ↔ P ∣ Q) := by
  let R := MvPolynomial (Fin N × ℕ) F
  let L := FractionRing R
  let P₀ := stripPolynomial P
  have hP₀ : Irreducible P₀ := irreducible_stripPolynomial hP
  let p := P₀.map (algebraMap R L)
  letI : Fact (Irreducible p) := ⟨irreducible_fraction_map hP₀ hdeg⟩
  let E := AdjoinRoot p
  have hroot := fraction_generic_strip_root P₀ hP₀ hdeg δ η hc hN
  change ∃ (D H : Derivation k E E) (v : E), _ at hroot
  obtain ⟨D, H, v, hDH, hD, hH, htop, hstrip, heq, hker, hsep⟩ := hroot
  let point := NewtonRoot.rootPoint (F := F) (σ := Fin N × ℕ) (L := L) (D^[N] v)
  let jets : Triangle N → E := fun ij ↦ D^[ij.val.1] (H^[ij.val.2] v)
  have hpoint : ∀ ij, point (stripIndex ij) = jets ij := by
    intro ij
    by_cases hi : ij.val.1 < N
    · simp only [stripIndex, dif_pos hi]
      exact (hstrip ij.val.1 ij.val.2 hi).symm
    · have hij := eq_leader_of_not_lt ij hi
      subst ij
      rw [stripIndex_leader]
      simp [point, NewtonRoot.rootPoint, jets, leader]
  have hvalue (Q : MvPolynomial (Triangle N) F) :
      MvPolynomial.aeval jets Q =
        Polynomial.aeval (D^[N] v) ((stripPolynomial Q).map (algebraMap R L)) := by
    rw [← aeval_strip_rename point jets hpoint Q]
    exact NewtonRoot.aeval_rootPoint (D^[N] v) (rename stripIndex Q)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    D, H, v, hDH, hD, hH, ?_, ?_, ?_⟩
  · rw [hvalue]
    exact heq
  · rw [hvalue, stripPolynomial_leader_pderiv]
    simpa only [Polynomial.derivative_map] using hsep
  · intro Q
    rw [hvalue, hker]
    exact stripPolynomial_dvd_iff P Q


end

end MakarLimanov.NewtonCKRoot
