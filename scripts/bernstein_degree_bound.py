#!/usr/bin/env python3
"""Compute an exact rational degree cutoff conditional on supplied L, gap.

The input is NOT obtained from a certified H. This script just implements
n = 1 + floor(24 L^2 / gamma^2) and checks the strict inequality.
"""
import argparse
from fractions import Fraction


def degree_bound(lipschitz: Fraction, safety_gap: Fraction) -> int:
    if lipschitz < 0:
        raise ValueError('Lipschitz constant L must be nonnegative')
    if safety_gap <= 0:
        raise ValueError('Safety gap gamma must be positive')
    threshold = 24 * lipschitz**2 / safety_gap**2
    n = (threshold.numerator // threshold.denominator) + 1
    assert n >= 1 and 24*lipschitz**2 < n*safety_gap**2
    return n


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('L', type=Fraction, help='a rational Lipschitz bound, e.g. 10/3')
    parser.add_argument('gamma', type=Fraction, help='a positive rational safety gap')
    args = parser.parse_args()
    n = degree_bound(args.L, args.gamma)
    print(f'L = {args.L}, gamma = {args.gamma}, sufficient Bernstein degree n = {n}')
    print('Verified exactly: 24 L^2 < n gamma^2')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
