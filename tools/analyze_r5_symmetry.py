#!/usr/bin/env python3
"""Exact-integer graph helpers for witness generation and regression tests.

These calculations are not Lean proofs. All certificates used by the final
result are checked separately by Lean. No legacy bundle, I/O, or network.
"""


def canonicalize(mask, s, ell):
    choices = []
    for direction in (1, -1):
        for shift in range(ell):
            p = [(direction * i + shift) % ell for i in range(ell)]
            moved = sum(1 << p[i] for i in range(ell) if mask >> i & 1)
            choices.append((moved, p))
    cycle, permutation = min(choices)
    selected = [i for i in range(ell, s) if mask >> i & 1]
    remaining = [i for i in range(ell, s) if not mask >> i & 1]
    for i in range(ell, s):
        permutation.append(ell + (selected + remaining).index(i))
    canonical = cycle | (((1 << len(selected)) - 1) << ell)
    assert sorted(permutation) == list(range(s))
    assert sum(1 << permutation[i] for i in range(s) if mask >> i & 1) == canonical
    # This is also checked computationally; the eventual Lean bridge must
    # prove bijectivity, adjacency preservation, and transport in general.
    def adjacent(i, j):
        return i != j and i < ell and j < ell and ((i + 1) % ell == j or (j + 1) % ell == i)
    assert all(adjacent(i, j) == adjacent(permutation[i], permutation[j])
               for i in range(s) for j in range(s))
    return canonical, permutation


def independent_masks(s, ell):
    return [m for m in range(1, 1 << s)
            if all(not ((m >> i & 1) and (m >> ((i + 1) % ell) & 1)) for i in range(ell))]


def check_row(mask, beta, weights, independent, bound):
    sums = [0] * (1 << len(weights))
    cards = [0] * len(sums)
    for subset in range(1, len(sums)):
        bit = subset & -subset
        previous = subset ^ bit
        sums[subset] = sums[previous] + weights[bit.bit_length() - 1]
        cards[subset] = cards[previous] + 1
    assert all(cards[i] <= beta for i in independent if i & mask == i)
    value = beta * sums[mask] + sum(
        max(0, bound[0] * cards[i] - sums[i & mask]) for i in independent if i & mask)
    assert value <= bound[1], (mask, beta, value, bound)
    return value
