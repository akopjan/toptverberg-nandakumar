#!/usr/bin/env python3
"""Exact rational sanity checks of the direct polynomial height formula.

For a rainbow source vector, evaluate BOTH (1) the full word-sum formula
and (2) the polynomial table evaluated at the masses. This verifies
specific finite instances including missing colors and does NOT replace
the quantified Lean theorem `polynomialHeight_rainbow`.
"""
from fractions import Fraction as F
from itertools import product
from random import Random

RNG = Random(20261023)
C = range(6)
LABELS = tuple(product(range(6), repeat=6))


def kernels(alpha, masses, selection):
    out = []
    for i in C:
        if alpha[i] == 0:
            out.append([F(1, 6) for _ in C])
        else:
            out.append([
                (masses[i] if a == selection[i] else F(0))
                * masses[i] ** (alpha[i]-1) for a in C])
    return out


def coefficient_table(alpha, word):
    # Deliberately depends only on i for which alpha_i > 0.
    return F(3) + sum(F((i+1)*(word[i]+1), 11)
                      for i in C if alpha[i] != 0)


def test_case(masses, selection, alpha):
    K = kernels(alpha, masses, selection)
    for i in C:
        assert sum(K[i]) == masses[i] ** alpha[i]
    lhs = F(0)
    for word in LABELS:
        term = coefficient_table(alpha, word)
        for i in C:
            term *= K[i][word[i]]
            if not term:
                break
        lhs += term
    rhs = coefficient_table(alpha, selection)
    for i in C:
        rhs *= masses[i] ** alpha[i]
    assert lhs == rhs, (lhs, rhs, alpha, masses, selection)


def main():
    alphas = [
        (0,0,0,0,0,0),
        (1,0,2,0,0,0),
        (0,1,1,0,3,0),
        (1,2,1,1,1,0),
        (0,0,0,0,0,4),
    ]
    cases = [
        (tuple(map(F, (F(1,3), F(2,3), 0, 0, 0, 0))), (0,1,2,3,4,5)),
        (tuple(F(1,6) for _ in C), (3,2,1,0,5,4)),
        (tuple(map(F, (0,0,0,F(1,1),0,0))), (4,4,4,4,4,4)),
    ]
    tests = 0
    for masses, selection in cases:
        assert sum(masses) == 1
        for alpha in alphas:
            test_case(masses, selection, alpha)
            tests += 1
    print(f'{tests} direct 46,656-word rational identities passed, including zero masses.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
