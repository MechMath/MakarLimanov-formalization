# Independent audit: separation and matrix realization

Source: `runs/makar-limanov-20260929/mmat/data/workspace/0e7dcc7f-6d6b-47e5-b157-1427684fbfab/proof.tex`, sections 3 and 6.

This is a mathematical source audit, not a Lean certificate. No counterexample or substantive mathematical gap was found in the portions below. This does not certify the Newton argument or the complete theorem.

## Section 3: generic separation

The separating representation is valid for each fixed polynomial. Bound its number of x letters by A. On the finite invariant space spanned by tau^j/j! for 0 <= j <= A, differentiation lowers j and the interpolation polynomial in tau*d/dtau acts diagonally by independent lambda_j. A word y^b0 x y^b1 ... x y^ba sends the top vector to the basis vector with index A-a, multiplied by the monomial with exponents b0,...,ba on successive lambda variables. Distinct words with equal x count yield distinct monomials; distinct x counts yield distinct output vectors. Thus cancellation cannot kill a nonzero free polynomial.

The auxiliary specialization b = sum c_j tau^j u^j also works. On finite Laurent symbols with nonnegative tau and u powers, the map tau^l u^q D^r -> tau^l D0^(r+q) preserves multiplication: the falling-factorial factor on either side is (r+q)_i, and the derivative of tau^m contributes (m)_i. Negative D0 exponents belong to the pseudodifferential symbol algebra; only the images of D and b, and consequently the evaluated free polynomial, need to be ordinary differential operators. Those images do have nonnegative differential degrees.

If every word contains x and k copies of y, the evaluated ordinary differential operator kills 1 and is nonzero. Its differential order is therefore at least 1. The u degree is at most A*k, so some source D exponent is at least 1-A*k. Polynomial specialization of finitely many jets cannot create a nonzero coefficient from an identically zero one. The lower bound follows.

The polarization argument in the variation lemma is also compatible with the noncommutative coefficient field issue: multilinearity is used over central auxiliary constants, while arbitrary coefficient inputs are substituted through differential jet polynomials. The central twists e_i D^r_i reduce monomial inputs to coefficient inputs. Fixed-coefficient truncation then reduces arbitrary upper-bounded symbols to finite sums.

## Section 6: infinite matrices

The matrix algebra is locally finite for multiplication despite its matrices generally being neither row-finite nor column-finite. For a path of fixed length, the upper jump bound on a gives both an upper bound from its initial endpoint and a lower bound from its terminal endpoint. The lower jump bound on c gives the complementary bounds. Every intermediate index belongs to a finite integer rectangle. This establishes finite sums and associativity without an invalid action on a direct-sum vector space.

The normal-ordering sign is correct. With L = partial_z + z^(-1)*partial_w and T = -L, multiplication operators satisfy M_B T - T M_B = M_(L B). Hence M_B T^k = sum_n binom(k,n) T^(k-n) M_(L^n B), exactly matching the diamond product.

For a fixed matrix entry of Q(P), a source monomial t^i w^j z^r must obey r = (a'-a)/p + i and j = b'-b + ell, where 0 <= ell <= i. Since r is bounded above, i is bounded and only finitely many monomials contribute. The fact that j can be unbounded in P therefore causes no undefined infinite sum.

For Q(P diamond Q), a contributing pair of source monomials satisfies

    (a'-a)/p = r+s-i-k
    b'-b = j+l-e-f, with e+f <= i+k.

Consequently i+k <= r_P+r_Q-(a'-a)/p and j+l <= b'-b+i+k. These bound the Taylor powers, while the fixed sum r+s together with individual upper bounds leaves finitely many lattice pairs r,s. All coefficient rearrangements in the homomorphism proof are therefore finite. No analytic convergence hypothesis is needed.

The jump inequalities follow from a monomial output: delta_a = p(r-i) <= p*r_P and delta_c = p(i+j-ell-r) >= -p*r_P. This is the exact support needed by compression.

## Finite compression

The square J with side p*S contains p*S^2 indices satisfying its congruence. An element of order at most -T has no surviving J entry when S <= T, because delta_a >= -(p*S-1) > -p*T there. The strict integer endpoint is correct.

The four boundary strips of thickness D*R*p control every word simultaneously. Away from the input and output strips, the same endpoint bounds force every intermediate path to remain in J. Thus compression error is supported in their common rows or columns, rather than requiring one independent rank bound per word. Each strip has at most D*R*p*S indices, including when its thickness exceeds the square side. Splitting a matrix into its designated rows and its remaining designated columns yields rank at most 4*D*R*p*S.

## Formalization caveats

These arguments require actual constructions of the symbol algebra, Taylor map, locally finite matrix algebra, and their multiplication laws. An abstract assumption that a suitable homomorphism or low-rank witness exists would leave the main realization obligation unproved. No Lean implementation of these constructions was added by this audit.
