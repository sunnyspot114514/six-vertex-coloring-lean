#!/usr/bin/env python3
"""Independently audit the bounded consecutive 3-full claim.

Uses only the Python standard library.  Enumerates the unique representations
n = a**3 * b**4 * c**5 with squarefree, coprime b and c, then compares the entire
result with trial factorization of every integer in [1, 100001].  It does not
read the Lean file or the certificate generator.  This numerical cross-check
is separate from Lean's kernel-checked prime-obstruction proof.
"""

import argparse
import json
from math import gcd, isqrt


UPPER = 100001
FIRST_MEMBER_UPPER = UPPER - 1


def require(condition, message):
    """Keep verification active even when Python is run with -O."""
    if not condition:
        raise RuntimeError(message)


def integer_root(n, exponent):
    """Floor of the positive integer exponent-th root; no floating point."""
    low, high = 0, n + 1
    while low + 1 < high:
        mid = (low + high) // 2
        if mid**exponent <= n:
            low = mid
        else:
            high = mid
    return low


def squarefree(n):
    return all(n % (d * d) != 0 for d in range(2, isqrt(n) + 1))


def representations(upper):
    """Generate all positive 3-full numbers up to upper, with unique triples."""
    limits = {"a": integer_root(upper, 3),
              "b": integer_root(upper, 4),
              "c": integer_root(upper, 5)}
    result = {}
    for a in range(1, limits["a"] + 1):
        for b in range(1, limits["b"] + 1):
            if not squarefree(b):
                continue
            for c in range(1, limits["c"] + 1):
                if gcd(b, c) != 1 or not squarefree(c):
                    continue
                n = a**3 * b**4 * c**5
                if n <= upper:
                    require(n not in result, f"Duplicate representation of {n}")
                    result[n] = (a, b, c)
    return result, limits


def trial_factorization(n):
    """Return all positive prime exponents by ordinary trial division."""
    factors = []
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            exponent = 0
            while n % divisor == 0:
                n //= divisor
                exponent += 1
            factors.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if n > 1:
        factors.append((n, 1))
    return factors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--details", action="store_true",
                        help="also print all 129 integers and their unique triples")
    args = parser.parse_args()

    generated, limits = representations(UPPER)
    factored = {
        n for n in range(1, UPPER + 1)
        if all(exponent >= 3 for _, exponent in trial_factorization(n))
    }
    require(set(generated) == factored,
            "Representation enumeration and trial factorization disagree")
    values = sorted(generated)
    consecutive = [[n, n + 1] for n in values
                   if n <= FIRST_MEMBER_UPPER and n + 1 in generated]
    gaps = [(right - left, left, right)
            for left, right in zip(values, values[1:])]
    minimum_gap = min(gap for gap, _, _ in gaps)
    minimum_gap_pairs = [[left, right] for gap, left, right in gaps
                         if gap == minimum_gap]

    def small_prime_obstruction(n):
        return any(
            m % p == 0 and m % (p**3) != 0
            for p in (2, 3, 5, 7) for m in (n, n + 1)
        )

    small_cases = sum(small_prime_obstruction(n)
                      for n in range(1, FIRST_MEMBER_UPPER + 1))
    require(len(values) == 129, "Unexpected 3-full count")
    require(not consecutive, "Found a consecutive 3-full pair")
    require(minimum_gap == 3 and minimum_gap_pairs == [[125, 128]],
            "Unexpected minimum-gap result")

    report = {
        "verified": True,
        "integer_interval_inclusive": [1, UPPER],
        "first_member_interval_inclusive": [1, FIRST_MEMBER_UPPER],
        "representation_limits": limits,
        "cube_full_count": len(values),
        "trial_factorization_count": len(factored),
        "trial_factorization_agrees": True,
        "unique_representations": True,
        "consecutive_pairs": consecutive,
        "minimum_gap": minimum_gap,
        "minimum_gap_pairs": minimum_gap_pairs,
        "last_five": values[-5:],
        "small_prime_obstruction_count": small_cases,
        "remaining_obstruction_count": FIRST_MEMBER_UPPER - small_cases,
        "scope": "Refutes only existence with 1 <= n <= 100000; no unbounded claim.",
    }
    if args.details:
        report["representations"] = [
            {"n": n, "a": generated[n][0], "b": generated[n][1],
             "c": generated[n][2]} for n in values
        ]
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
