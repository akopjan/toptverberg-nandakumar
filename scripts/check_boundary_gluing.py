#!/usr/bin/env python3
"""Exact rational test of the 41-layer boundary formula and gluing.

This checks endpoint values, layer transitions, and pairwise facet overlaps
for finite sample points and words. It does not prove all-dimensional
continuity or avoidance of any forbidden affine subspace.
"""
from fractions import Fraction as F
from itertools import combinations
from random import Random

R = Random(20261023)
COLORS = tuple(range(6))
POSITIVES = [frozenset(A) for k in (1,2) for A in combinations(COLORS, k)]
NEGATIVES = [frozenset(A) for A in combinations(COLORS, 3)]
MASKS = [POSITIVES[j//2] if j%2==0 else NEGATIVES[j//2]
         for j in range(41)]
assert MASKS[::2] == POSITIVES and MASKS[1::2] == NEGATIVES
assert len(MASKS) == 41
HEIGHTS = [[F(R.randrange(-20,21)) for a in COLORS] for i in COLORS]


def init(l, word):
    return sum(l[i]*HEIGHTS[i][word[i]] for i in COLORS)


def facet_center(missing):
    return tuple(F(0) if i == missing else F(1,5) for i in COLORS)


def anchor(base, A, word):
    return F(6) * (word[base] in A) - len(A)


def lerp(a,b,t):
    return (1-t)*a + t*b


def filling(missing, A, rho, theta, word):
    base = 0 if missing != 0 else 1
    q = init(facet_center(missing), word)
    p = HEIGHTS[base][word[base]]
    c = anchor(base,A,word)
    if rho <= F(1,4):
        return lerp(q,p,4*rho)
    if rho <= F(1,2):
        return lerp(p,c,4*rho-1)
    return lerp(c,init(theta,word),2*rho-1)


def facet_table(missing,l,word):
    m=min(l[i] for i in COLORS if i!=missing)
    r=1-5*m
    theta = (facet_center(missing) if r == 0 else
             tuple(F(0) if i==missing else (l[i]-m)/r for i in COLORS))
    j=min(40,(41*r).__floor__())
    progress=41*r-j
    rho=progress if j%2==0 else 1-progress
    return filling(missing,MASKS[j],rho,theta,word)


def boundary(l,word):
    zeros=[i for i in COLORS if l[i]==0]
    return facet_table(min(zeros),l,word)


def mix(a,b,t):
    return tuple((1-t)*a[i]+t*b[i] for i in COLORS)


def test():
    words=[tuple(R.randrange(6) for _ in COLORS) for j in range(12)]
    checks=0
    for missing in COLORS:
        center=facet_center(missing)
        corner=tuple(F(1) if i==((missing+1)%6) else F(0) for i in COLORS)
        for j in range(42):
            l=mix(center,corner,F(j,41))
            for word in words:
                value=facet_table(missing,l,word)
                if j==0:
                    assert value==init(center,word)
                if j==41:
                    assert value==init(corner,word)
                if j%2==0 and 0<j<41:
                    assert value==init(center,word)
                if j%2==1 and 0<j<41:
                    assert value==init(corner,word)
                checks+=1
    for missing1,missing2 in combinations(COLORS,2):
        others=[i for i in COLORS if i not in (missing1,missing2)]
        l=tuple(F(0) if i in (missing1,missing2) else F(1,len(others))
                for i in COLORS)
        for word in words:
            assert facet_table(missing1,l,word) == init(l,word)
            assert facet_table(missing2,l,word) == init(l,word)
            assert boundary(l,word) == init(l,word)
            checks+=1
    print(f'{checks} exact rational boundary-gluing checks passed (41 layers, all facets).')
    return 0


if __name__ == '__main__':
    raise SystemExit(test())
