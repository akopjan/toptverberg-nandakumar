#!/usr/bin/env python3
"""Finite modular non-vanishing tests for the ORIGINAL huge integer seeds.

If det modulo prime != 0, the corresponding integer determinant is nonzero.
This is not a proof for ALL (720**6) ordered matchings.
"""
from itertools import combinations
from random import Random

PRIME = 2305843009213693951  # 2^61 - 1
BASE = 65536
N = 6
HEIGHTS = [[pow(BASE, (7 ** i) * (a + 1), PRIME) for a in range(N)]
           for i in range(N)]


def det_mod(M):
    n = len(M)
    A = [[x % PRIME for x in row] for row in M]
    d = 1
    for j in range(n):
        r = next((k for k in range(j,n) if A[k][j]), None)
        if r is None: return 0
        if r != j:
            A[j],A[r] = A[r],A[j]
            d = -d
        a = A[j][j]
        d = d * a % PRIME
        inv = pow(a, -1, PRIME)
        for k in range(j+1,n):
            factor = A[k][j]*inv % PRIME
            if factor:
                for l in range(j+1,n):
                    A[k][l] = (A[k][l]-factor*A[j][l])%PRIME
            A[k][j] = 0
    return d % PRIME


def normals(perms):
    return [[(HEIGHTS[i][perms[i][j]]-HEIGHTS[i][perms[i][5]])%PRIME
             for j in range(5)] for i in range(N)]


def check_one(perms):
    v = normals(perms)
    augmented = [[v[i][j] for i in range(6)] for j in range(5)] + [[1]*6]
    if not det_mod(augmented): return 'augmented'
    for omission in range(6):
        J = [i for i in range(6) if i != omission]
        matrix = [[v[i][j] for i in J] for j in range(5)]
        if not det_mod(matrix): return ('facet',omission)
    for colors in combinations(range(6),4):
        for sz in range(1,6):
            for A in combinations(range(6),sz):
                u = [6*((j in A) - (5 in A)) for j in range(5)]
                matrix = [[u[j]] + [v[i][j] for i in colors] for j in range(5)]
                if not det_mod(matrix): return ('anchor',colors,A)
    return None


def main(count=80):
    rand = Random(20261023)
    tested = 0
    for t in range(count):
        perms = [rand.sample(list(range(6)),6) for _ in range(6)]
        bad = check_one(perms)
        if bad:
            print('Modular failure:',t,bad,'perms',perms)
            return 1
        tested += 1
    print(f'{tested} matchings verified mod {PRIME};')
    print(f'Actual number of anchor determinants: {tested * 15 * 62}')
    print('All modular checks passed; this does NOT establish universal genericity.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
