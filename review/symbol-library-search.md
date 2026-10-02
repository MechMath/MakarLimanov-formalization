# Symbol algebra and differential-extension library search

Source inspected: the local mathlib tree at
`/Users/tsuki/Desktop/SunMatrix/.lake/packages/mathlib/Mathlib`, and sections 3–4 of
the submitted `proof.tex`. This is a source search and architecture review, not a
Lean certification of the submitted lemmas.

## Recommended symbol representation

For each positive denominator `p`, use a wrapper around `LaurentSeries F`
(`HahnSeries ℤ F`), interpreting coefficient index `n` as exponent `-n/p` of D.
This converts the proof's upper-bounded discrete support into the library's
lower-bounded support. Keep the ordinary commutative series ring on the underlying
type and the new star multiplication on a distinct wrapper to avoid conflicting
ring instances. Using arbitrary `HahnSeries ℚ F` without a discrete-support
restriction would enlarge the statement and lose the elementary finiteness bound.

Under this convention, Δ maps coefficient `a` at index `n` to
`(-(n : F)/(p : F) * a + η a)` at index `n+p`; δ acts coefficientwise.
Coefficient derivation can use `HahnSeries.map` with a zero-preserving map.
The Euler coefficient map and shift, their Leibniz rules, and commutation must
still be proved. The existing ordinary Laurent derivative differentiates the
Laurent variable, so it is not directly this Δ.

The star-product family is indexed by `j : ℕ`, with term
`(j! : F)⁻¹ • (Δ^[j] U * δ^[j] V)`. Build an explicit
`HahnSeries.SummableFamily` using the order estimate that its term has order at
least `order U + order V + p*j`. Then use `hsum`. The finite co-support obligation
is essential; `hsum` does not remove the need to prove local finiteness.

Reusable declarations (all under `Mathlib/RingTheory/HahnSeries`):

- `Basic.lean`: `HahnSeries.map`, `orderTop`, `coeff_eq_zero_of_lt_orderTop`,
  `orderTop_le_of_coeff_ne_zero`, `embDomain`, `embDomain_coeff`,
  `embDomain_injective`, `orderTop_embDomain`.
- `Multiplication.lean`: `coeff_mul`, `coeff_single_mul`, `single_mul_single`,
  `orderTop_mul`, `orderTop_add_le_mul`, `embDomain_mul`, `embDomainRingHom`,
  `embDomainAlgHom`.
- `Summable.lean`: `SummableFamily`, `SummableFamily.coeff_hsum`,
  `SummableFamily.coeff_hsum_eq_sum_of_subset`, `SummableFamily.hsum_add`,
  `SummableFamily.hsum_mul`, `SummableFamily.hsum_equiv`.
- `Mathlib/RingTheory/LaurentSeries.lean`: `LaurentSeries.hasseDeriv`,
  `hasseDeriv_coeff`, `derivative`, `derivative_iterate`, `derivative_iterate_coeff`.

Denominator enlargement from `p` to `p*q` is the exponent embedding `n ↦ q*n`;
`embDomainRingHom` supplies the ordinary ring map. Star compatibility still needs
the coefficient identities for Δ with the two denominator parameters.

The tree has no discovered `WeylAlgebra`, `OrePolynomial`, deformation quantization,
or matching associative star-product implementation. The Ore localization files
concern localization of noncommutative rings, not differential Ore polynomials.
Associativity of the submitted star product remains a substantial new theorem:
iterated Leibniz expansion, coefficientwise finite triple sums, index bijection,
and factorial identities.

## Differential fields and PDE realization

`Mathlib/FieldTheory/Differential/Basic.lean` contains useful genuine extension
machinery, in namespace `Differential`:

- An instance `Differential (AdjoinRoot p)` for a monic irreducible polynomial over
  a characteristic-zero differential field.
- The corresponding `DifferentialAlgebra F (AdjoinRoot p)` instance.
- `differentialFiniteDimensional F K`.
- `differentialAlgebraFiniteDimensional`.
- `uniqueDifferentialAlgebraFiniteDimensional`.

These handle a derivation `F → F` extended to a finite field extension, and the
uniqueness theorem packages equality of compatible differential structures.
They do not directly supply the more general derivation `K → E` used in the
submitted PDE construction before extending to `E → E`.

Additional concrete building blocks:

- `Mathlib/RingTheory/Derivation/Basic.lean`: `Derivation.liftOfSurjective`,
  `liftOfSurjective_apply`, `compAlgebraMap`, `leibniz_inv`, `leibniz_div`,
  `ext_of_adjoin_eq_top`.
- `Mathlib/RingTheory/Derivation/MapCoeffs.lean`: `Derivation.mapCoeffs`,
  `Derivation.apply_aeval_eq'`, `Derivation.apply_aeval_eq`,
  `Differential.implicitDeriv`, `Differential.deriv_aeval_eq`,
  `Differential.algHom_deriv`.
- `Mathlib/Algebra/MvPolynomial/Derivation.lean`:
  `MvPolynomial.mkDerivation`, `mkDerivation_X`, `mkDerivation_monomial`,
  `mkDerivationEquiv`, `derivation_ext`.
- `Mathlib/RingTheory/Derivation/Lie.lean`:
  `Derivation.commutator_apply`; the commutator is a derivation.

Two cautions: `MvPolynomial.mkDerivation F` kills all coefficients in F, whereas
the jets in the proof have already nonzero coefficient derivations; add a
coefficientwise derivation as well. `Derivation.leibniz_div` proves a property of
an existing derivation and is not itself a constructor for a fraction-field
extension.

No ready-made two-commuting-derivation differential polynomial ring, differential
closure, or single-PDE-with-inequations realization theorem was found in this
tree. The submitted section 4 therefore needs a new construction. Its main tasks
are the finite jet coordinate change, embedding the hypersurface domain in the
fraction field, extending derivations with larger codomain, commuting the two
extensions, and proving the evaluation kernel is exactly the principal ideal.
The scalar (`N=0`) branch has much more existing support than the general branch.

For two derivations, retain explicit `Derivation k F F` fields and an explicit
commutation proof; using two simultaneous `Differential F` typeclass instances
would make elaboration ambiguous. The existing differential-field extension
instances can be used locally for each derivation and converted back to explicit
objects.
