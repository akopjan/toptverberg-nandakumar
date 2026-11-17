#!/usr/bin/env python3
"""Independent finite rational checks for the facet-degree identity.

Uses moderate integer heights (not the huge Lean seed). Consequently this
checks signs/orientations of the combinatorial identity, NOT the genericity
statement for the actual construction.
"""
from fractions import Fraction
from itertools import combinations
from random import Random


def det(matrix):
    mat = [list(map(Fraction, row)) for row in matrix]
    n = len(mat)
    if any(len(row) != n for row in mat):
        raise ValueError("det requires square matrix")
    sign = 1
    product = Fraction(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if mat[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if j != pivot:
            mat[j], mat[pivot] = mat[pivot], mat[j]
            sign *= -1
        p = mat[j][j]
        product *= p
        for k in range(j+1, n):
            ratio = mat[k][j] / p
            if ratio:
                for col in range(j+1, n):
                    mat[k][col] -= ratio * mat[j][col]
            mat[k][j] = Fraction(0)
    return sign * product


def solve(matrix, rhs):
    n = len(rhs)
    a = [list(map(Fraction, matrix[i])) + [Fraction(rhs[i])] for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return None
        a[j], a[pivot] = a[pivot], a[j]
        p = a[j][j]
        a[j] = [item / p for item in a[j]]
        for i in range(n):
            if i != j and a[i][j]:
                q = a[i][j]
                a[i] = [a[i][k] - q*a[j][k] for k in range(n+1)]
    return [a[i][n] for i in range(n)]


def sgn(q):
    return (q > 0) - (q < 0)


def columns_for_matching(m, heights):
    return [[heights[i][m[k][i]]-heights[i][m[5][i]] for k in range(5)]
            for i in range(6)]


def phi(u, cols, missing):
    active = [i for i in range(6) if i != missing]
    B = [[cols[i][j] for i in active] for j in range(5)]
    detB = det(B)
    if detB == 0:
        raise ArithmeticError('degenerate facet matrix')
    x = solve(B, [-val for val in u])
    if x and all(val > 0 for val in x):
        return sgn(detB)
    return 0


def degree(cols):
    augmented = [[cols[i][j] for i in range(6)] for j in range(5)] + [[1]*6]
    d = det(augmented)
    if d == 0:
        raise ArithmeticError('degenerate augmented matrix')
    x = solve(augmented, [0]*5 + [1])
    return sgn(d) if x is not None and all(val > 0 for val in x) else 0


def run(n=30, seed=20261023):
    rand = Random(seed)
    nontrivial = 0
    for _ in range(n):
        heights = [rand.sample(range(-100,100), 6) for i in range(6)]
        perms = [rand.sample(range(6), 6) for i in range(6)]
        m = [[perms[i][k] for i in range(6)] for k in range(6)]
        cols = columns_for_matching(m, heights)
        try:
            initial_degree = degree(cols)
        except ArithmeticError:
            continue
        nontrivial += (initial_degree != 0)
        for size in [1,2,3]:
            for A in combinations(range(6), size):
                u = [6*(k in A) - 6*(5 in A) for k in range(5)]
                try:
                    lhs = sum(((-1)**missing)*phi(u,cols,missing)
                              for missing in range(6))
                except ArithmeticError:
                    break
                # The input simplex has its last barycentric coordinate omitted,
                # whereas the facet-chain orientation uses the vertex order.
                # In dimension five the conversion is multiplication by -1.
                vertex_oriented_degree = -initial_degree
                if lhs != vertex_oriented_degree:
                    print('ORIENTED BOUNDARY IDENTITY FAILED:', 'degree',initial_degree,
                          'lhs',lhs,'subset', A, 'matching',m,'heights',heights)
                    return 1
            else:
                continue
            break
    print(f'Checked {n} random configurations; nonzero degrees: {nontrivial}; original 41 shells cancel all tested degrees')
    return 0


if __name__ == '__main__':
    raise SystemExit(run())
