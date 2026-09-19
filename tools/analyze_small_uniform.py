#!/usr/bin/env python3
"""Explore uniform dual weights using exact integers; this is NOT a proof.

No network or filesystem writes. The Lean certificate checks are independent:
they check both beta validity and the full dual inequality for every subset.
"""
import argparse
from collections import Counter
import json

from analyze_r5_symmetry import independent_masks


def uniform_rows(s, ell):
    """Return (mask, beta, twice-weight, twice-bound), including the empty set."""
    if not (5 <= ell <= s <= 10 and ell % 2 == 1):
        raise ValueError("expected an odd cycle length with 5 <= ell <= s <= 10")
    types = independent_masks(s, ell)
    cards = [bin(m).count("1") for m in range(1 << s)]
    rows = [(0, 0, 0, 0)]
    for mask in range(1, 1 << s):
        beta = max(cards[i] for i in types if i & mask == i)
        histogram = Counter((cards[i], cards[i & mask]) for i in types if i & mask)
        candidates = [
            (beta * weight * cards[mask] + sum(
                count * max(0, 2 * size - weight * overlap)
                for (size, overlap), count in histogram.items()), weight)
            for weight in range(2 * s + 1)
        ]
        value, weight = min(candidates)
        rows.append((mask, beta, weight, value))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, choices=(8, 9, 10), action="append")
    args = parser.parse_args()
    families = []
    for s in args.size or (8, 9, 10):
        for ell in range(5, s + 1, 2):
            rows = uniform_rows(s, ell)
            bound = max(row[3] for row in rows)
            families.append(dict(size=s, cycle=ell, masks=len(rows), scale=2,
                                 scaled_bound=bound, surplus_bound=bound // 2))
    print(json.dumps(dict(status="EXPERIMENT_NOT_LEAN_PROOF", families=families), indent=2))


if __name__ == "__main__":
    main()
