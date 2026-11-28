#!/usr/bin/env python3
"""Reproduce and independently cross-check the A245211 count-69 obstruction.

Standard library only. This is finite computational evidence, not a Lean proof.
Run: python audit_count69.py [output.json]

Underlying proved structural theorem used conditionally:
a squarefree fixed point with r distinct prime factors gives a prime cycle
    2*p[i+1] + 1 = d[i]*p[i],  product(d) = 2**r + 1,
with every p[i] > 2**(r-1). Allocating every prime occurrence of the product
to one multiplier, and rotating a chosen token to position zero, is exhaustive.
"""
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path
import json
import sys
import time

R = 69
TOKENS = (3, 3, 139, 2796203, 168749965921)
MODULI = (3, 5, 7, 11, 13)


def is_prime(n):
    """Deterministic trial division, not a probable-prime test."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def coefficients(q, positions):
    """Tokens omitted from a projection must be congruent to one mod q.

    positions maps labelled token indices to cycle positions. Different tokens,
    including the two occurrences of 3, may share a position.
    """
    assert q > 1 and q % 2 == 1
    assert all(isinstance(i, int) and 0 <= i < len(TOKENS)
               and isinstance(j, int) and 0 <= j < R
               for i, j in positions.items())
    ds = [1] * R
    for i, token in enumerate(TOKENS):
        if i in positions:
            j = positions[i]
            ds[j] = ds[j] * token % q
        else:
            assert token % q == 1, (q, i, token)
    assert (prod(ds) - pow(2, R, q)) % q == 1
    return ds


def seed_admissible(q, positions):
    """Use the unique closed seed, then require every prime residue to be a unit.

    S[0]=0 and S[k+1]=d[k]*S[k]+2**k.
    The exact recurrence implies
      2**r*p[r] + S[r] = product(d)*p[0].
    Closure and product(d)=2**r+1 therefore imply p[0]=S[r] exactly.
    All operations below are integer arithmetic modulo q; division by 2 uses
    (q+1)//2, whose inverse property is asserted explicitly.
    """
    ds = coefficients(q, positions)
    inverse_two = (q + 1) // 2
    assert 2 * inverse_two % q == 1
    seed, two_power = 0, 1
    for d in ds:
        seed = (d * seed + two_power) % q
        two_power = 2 * two_power % q
    x = seed
    for d in ds:
        if gcd(x, q) != 1:
            return False
        x = ((d * x - 1) * inverse_two) % q
    assert x == seed
    return True


def brute_closed_admissible(q, positions):
    """Independent algorithm: try every start, with no seed formula."""
    ds = coefficients(q, positions)
    inverse_two = pow(2, -1, q)
    for start in range(q):
        x = start
        for d in ds:
            if gcd(x, q) != 1:
                break
            x = ((d * x - 1) * inverse_two) % q
        else:
            if x == start:
                return True
    return False


def full_positions(row):
    """row=(a,b,c,d) means token positions (0,a,b,c,d)."""
    assert len(row) == 4
    return dict(enumerate((0, *row)))


def first_nonunit_trace(q, row):
    ds = coefficients(q, full_positions(row))
    seed, power = 0, 1
    for d in ds:
        seed = (d * seed + power) % q
        power = 2 * power % q
    x, trace = seed, []
    for i, d in enumerate(ds):
        trace.append(x)
        if gcd(x, q) != 1:
            return {"positions_abcd": row, "seed": seed,
                    "first_nonunit_index": i, "residue_trace": trace}
        x = ((d * x - 1) * ((q + 1) // 2)) % q
    raise AssertionError(("unexpected admissible row", q, row))


def main():
    started = time.perf_counter()
    assert prod(TOKENS) == 2**R + 1
    assert all(is_prime(p) for p in TOKENS)
    assert max(MODULI) < 2**(R - 1)

    # dot's route: modulo 5 ignores only token 4, which is 1 mod 5.
    projected5 = [
        (a, b, c) for a, b, c in product(range(R), repeat=3)
        if seed_admissible(5, {0: 0, 1: a, 2: b, 3: c})
    ]
    assert len(projected5) == 412
    after5 = [(*abc, d) for abc in projected5 for d in range(R)]
    assert len(after5) == 28428
    after7 = [row for row in after5 if seed_admissible(7, full_positions(row))]
    after11 = [row for row in after7 if seed_admissible(11, full_positions(row))]
    after13 = [row for row in after11 if seed_admissible(13, full_positions(row))]
    assert (len(after7), len(after11), len(after13)) == (3547, 14, 0)

    # Smaller certificate: use modulus 3 before modulo 5.
    stage3 = [
        (a, c) for a, c in product(range(R), repeat=2)
        if seed_admissible(3, {0: 0, 1: a, 3: c})
    ]
    assert stage3 == [(0, 1), (1, 2), (68, 1)]
    stage5 = [
        (a, b, c) for a, c in stage3 for b in range(R)
        if seed_admissible(5, {0: 0, 1: a, 2: b, 3: c})
    ]
    assert stage5 == [(1, 4, 2), (68, 3, 1)]
    expanded = [(*abc, d) for abc in stage5 for d in range(R)]
    assert len(expanded) == 138
    stage7 = [row for row in expanded if seed_admissible(7, full_positions(row))]
    assert stage7 == [(1, 4, 2, 3), (1, 4, 2, 68),
                      (68, 3, 1, 2), (68, 3, 1, 67)]
    stage11 = [row for row in stage7 if seed_admissible(11, full_positions(row))]
    assert stage11 == []

    # Independently recheck the whole shorter route by exhaustive start search.
    brute3 = [
        (a, c) for a, c in product(range(R), repeat=2)
        if brute_closed_admissible(3, {0: 0, 1: a, 3: c})
    ]
    brute5 = [
        (a, b, c) for a, c in brute3 for b in range(R)
        if brute_closed_admissible(5, {0: 0, 1: a, 2: b, 3: c})
    ]
    brute7 = [
        (*abc, d) for abc in brute5 for d in range(R)
        if brute_closed_admissible(7, full_positions((*abc, d)))
    ]
    brute11 = [row for row in brute7
               if brute_closed_admissible(11, full_positions(row))]
    assert (brute3, brute5, brute7, brute11) == (stage3, stage5, stage7, stage11)
    assert all(brute_closed_admissible(11, full_positions(row)) for row in after11)
    assert not any(brute_closed_admissible(13, full_positions(row)) for row in after11)

    report = {
        "target": {
            "sequence": "OEIS A245211",
            "hypotheses": "Squarefree n and n.primeFactors.card = 69",
            "conclusion": "OeisA245211.a n != n",
            "upper_bound_on_n": None,
            "status": "finite computational obstruction; not a Lean proof",
            "remaining_branch": "OeisA245211.conjecture.R2.H3.R1.H2",
        },
        "factorization": {
            "two_to_69_plus_one": str(2**R + 1),
            "prime_tokens": TOKENS,
            "product_matches": True,
            "all_tokens_prime": True,
            "primality_method": "deterministic odd trial division through floor(sqrt(p))",
            "largest_trial_divisor_bound": isqrt(max(TOKENS)),
            "prime_lower_bound_strict": str(2**(R - 1)),
        },
        "definitions": {
            "indexing": "indices and positions are zero based",
            "position_tuple": "(a,b,c,d) gives token positions (0,a,b,c,d)",
            "recurrence": "2*p[(i+1) mod 69]+1 = d[i]*p[i]",
            "product": "product(d)=2^69+1",
            "seed": "S[0]=0; S[k+1]=d[k]*S[k]+2^k; p[0]=S[69]",
            "modular_step": "x_next=(d*x-1)*inverse(2) mod q",
            "denominator": "q odd, so inverse(2)=(q+1)//2 exists",
            "admissible": "the unique closed residue trace is coprime to q everywhere",
        },
        "coverage_and_soundness": [
            "Each occurrence of a prime is a separately labelled token, including the two 3s.",
            "Every token is assigned to exactly one of 69 positions; arbitrary collisions are allowed.",
            "Cyclic translation fixes the first labelled 3 at position 0 without excluding any allocation.",
            "The normalized full position space has 69^4 assignments.",
            "A projection omits only factors equal to 1 modulo that modulus; the code asserts this condition.",
            "Surviving position tuples retain the same assignments when passed to subsequent moduli.",
            "The product identity makes the closed initial residue unique, even if a coefficient is zero.",
            "Every actual cycle prime is greater than 2^68, hence coprime to each checked prime modulus.",
            "Exhaustive modular rejection is a necessary-condition contradiction; no bound on n is searched.",
            "The connection from fixed points to prime-token cycles relies on the existing Lean structural theorem.",
        ],
        "dot_route": {
            "normalized_full_position_count": R**4,
            "mod5_projected_position_count": R**3,
            "mod5_projected_survivor_count": len(projected5),
            "after_restoring_neutral_token_positions": len(after5),
            "after_mod7_count": len(after7),
            "after_mod11_count": len(after11),
            "after_mod11_positions_abcd": after11,
            "after_mod13_count": len(after13),
            "after_mod13_positions_abcd": after13,
        },
        "smaller_route": {
            "mod3_projected_position_count": R**2,
            "after_mod3_positions_ac": stage3,
            "mod5_projected_extensions_checked": len(stage3)*R,
            "after_mod5_positions_abc": stage5,
            "after_restoring_last_token_positions": len(expanded),
            "after_mod7_positions_abcd": stage7,
            "after_mod11_positions_abcd": stage11,
            "mod11_rejection_traces": [first_nonunit_trace(11, row) for row in stage7],
            "mod13_needed": False,
        },
        "independent_algorithm": {
            "method": "enumerate every starting residue, test unit walk and cyclic closure",
            "uses_seed_formula": False,
            "whole_smaller_route_matches": True,
            "dot_last_14_cases_mod11_and_mod13_match": True,
        },
        "lean_status": {
            "formalized_here": False,
            "needed": "kernel-check the finite tables and combine them with the existing cycle and projection theorems",
            "native_decide_used": False,
            "external_oracle_accepted_by_lean": False,
        },
    }
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("audit_count69.json")
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("dot route: 69^3 -> 412, restore token -> 28428 -> 3547 -> 14 -> 0")
    print("smaller route: 69^2 -> 3 -> 2, restore token -> 138 -> 4 -> 0")
    print("Independent exhaustive-start cross-check passed.")
    print(f"Report: {target}; elapsed {time.perf_counter()-started:.3f}s")


if __name__ == "__main__":
    main()

