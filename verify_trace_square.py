#!/usr/bin/env python3
"""Verify tr(P) = tr(P^2) = 0 for two generic 3-by-3 matrices.

Here P = [X, [Y,X] [X,[Y,X]^2]], with [A,B] = AB - BA.
All entries lie in ZZ[x_11,...,x_33,y_11,...,y_33].  The 18 variables
are independent and commuting; matrix multiplication is noncommutative.
Every operation expands and collects integer polynomial coefficients.

Install: python -m pip install sympy
Run:     python verify_trace_square.py
"""

from time import perf_counter

from sympy import ZZ
from sympy.polys.rings import ring


def matmul(A, B):
    return [
        [sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)]
        for i in range(3)
    ]


def commutator(A, B):
    AB, BA = matmul(A, B), matmul(B, A)
    return [[AB[i][j] - BA[i][j] for j in range(3)] for i in range(3)]


def main():
    start = perf_counter()
    names = tuple(
        f"{letter}_{i}{j}"
        for letter in ("x", "y")
        for i in range(1, 4)
        for j in range(1, 4)
    )
    polynomial_ring, *variables = ring(names, ZZ)
    X = [[variables[3 * i + j] for j in range(3)] for i in range(3)]
    Y = [[variables[9 + 3 * i + j] for j in range(3)] for i in range(3)]
    print("Exact coefficient ring: ZZ[" + ", ".join(names) + "]", flush=True)

    C = commutator(Y, X)
    C_squared = matmul(C, C)
    P = commutator(X, matmul(C, commutator(X, C_squared)))
    print("P expanded in all 18 independent variables.", flush=True)

    trace_P = sum(P[i][i] for i in range(3))
    # tr(P^2) = sum_{i,j} P_ij P_ji; no other entries of P^2 are needed.
    trace_P_squared = sum(P[i][i] ** 2 for i in range(3))
    trace_P_squared += 2 * sum(P[i][j] * P[j][i] for i in range(3) for j in range(i + 1, 3))
    print("tr(P)   =", trace_P, flush=True)
    print("tr(P^2) =", trace_P_squared, flush=True)
    if trace_P != 0 or trace_P_squared != 0:
        raise AssertionError("A trace polynomial did not vanish identically.")
    print("Verified: both are the zero polynomial over ZZ.")
    print(f"Elapsed time: {perf_counter() - start:.2f} seconds")


if __name__ == "__main__":
    main()
