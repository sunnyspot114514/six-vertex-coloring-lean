from math import gcd
from time import perf_counter
import sys

FACTORS = {
    15: [3, 3, 11, 331], 21: [3, 3, 43, 5419],
    33: [3, 3, 67, 683, 20857], 35: [3, 11, 43, 281, 86171],
    39: [3, 3, 2731, 22366891],
    45: [3, 3, 3, 11, 19, 331, 18837001],
    51: [3, 3, 307, 2857, 6529, 43691],
    55: [3, 11, 11, 683, 2971, 48912491],
    57: [3, 3, 571, 174763, 160465489],
    63: [3, 3, 3, 19, 43, 5419, 77158673929],
}

def check(r, modulus):
    factors = [f % modulus for f in FACTORS[r] if f % modulus != 1]
    full = (1 << len(factors)) - 1
    units = [p for p in range(modulus) if gcd(p, modulus) == 1]
    unit_ix = {p: i for i, p in enumerate(units)}
    width = len(units)
    values = [1] * (full + 1)
    for mask in range(1, full + 1):
        bit = mask & -mask
        values[mask] = values[mask ^ bit] * factors[bit.bit_length() - 1] % modulus
    vt = {}
    for value in set(values):
        g = gcd(value, modulus)
        small_mod = modulus // g
        inverse = pow(value // g, -1, small_mod) if small_mod > 1 else 0
        vt[value] = {}
        for p in units:
            a = (2*p + 1) % modulus
            zs = []
            if a % g == 0:
                z0 = (a // g * inverse) % small_mod
                zs = [unit_ix[z] for j in range(g)
                      if (z := z0 + j * small_mod) in unit_ix]
            vt[value][p] = zs
    transitions = [[] for _ in range((full + 1) * width)]
    for remaining in range(full + 1):
        for pi, p in enumerate(units):
            out = transitions[remaining * width + pi]
            consumed = remaining
            while True:
                next_base = (remaining ^ consumed) * width
                out.extend(next_base + z for z in vt[values[consumed]][p])
                if consumed == 0:
                    break
                consumed = (consumed - 1) & remaining
    max_states = 0
    for initial in range(width):
        states = {full * width + initial}
        for _ in range(r):
            states = {z for state in states for z in transitions[state]}
            max_states = max(max_states, len(states))
        if initial in states:
            return True, len(factors), max_states
    return False, len(factors), max_states

if __name__ == '__main__':
    rs = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else [35,45,51,55]
    moduli = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [255,273,285,315,357,399,429,465,495,561,609,651,663,735,759,861,897,935,1001,1155,1365,15015]
    for r in rs:
        for modulus in moduli:
            start = perf_counter()
            answer = check(r, modulus)
            print(r, modulus, answer, round(perf_counter()-start,3), flush=True)
            if not answer[0]:
                break
