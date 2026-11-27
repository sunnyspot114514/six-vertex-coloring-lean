"""Small staged position checks for the exact A245211 R2 H2 target.

Independent finite arithmetic evidence, to be rechecked by Lean's kernel.
Token indices use FACTORS from search_moduli.py; repeated primes are separate
labelled tokens.  The caller's cyclic rotation fixes the stated token at 0.

Direction: 2*p[i+1]+1 = d[i]*p[i], with prod(d)=2**r+1.
If S[0]=0 and S[j+1]=d[j]*S[j]+2**j, then closure forces p[0]=S[r].
All computations here are modulo the chosen odd modulus q.  A projected
position list may omit only tokens congruent to 1 modulo q.
"""
from itertools import product
from math import gcd, prod
from pathlib import Path
import json
from time import perf_counter
from search_moduli import FACTORS


def coefficients(r, modulus, positions):
    """positions is a dict token-index -> position; missing tokens must be 1 mod q."""
    values = [1] * r
    for token, factor in enumerate(FACTORS[r]):
        if token in positions:
            place = positions[token]
            assert 0 <= place < r
            values[place] = values[place] * factor % modulus
        else:
            assert factor % modulus == 1, (r, modulus, token, factor)
    return values


def trace_is_admissible(r, modulus, positions):
    """Unique closed residue trace contains only residues coprime to modulus."""
    assert modulus > 1 and modulus % 2 == 1
    ds = coefficients(r, modulus, positions)
    s, two_power = 0, 1
    for d in ds:
        s = (d * s + two_power) % modulus
        two_power = 2 * two_power % modulus
    x = initial = s
    inverse_two = (modulus + 1) // 2
    for d in ds:
        if gcd(x, modulus) != 1:
            return False
        x = ((d * x + modulus - 1) * inverse_two) % modulus
    assert x == initial, (r, modulus, positions, initial, x)
    return True


def r45_certificates():
    # Normalize token 3, the unique factor 11, at position zero.
    stage1 = [abc for abc in product(range(45), repeat=3)
              if trace_is_admissible(45, 3, {0:abc[0], 1:abc[1], 2:abc[2], 3:0})]
    assert len(stage1) == 13
    stage2 = [(*abc, a) for abc in stage1 for a in range(45)
              if trace_is_admissible(45, 5, {0:abc[0], 1:abc[1], 2:abc[2], 3:0, 4:a})]
    assert len(stage2) == 13
    after7, after13, after19 = [], [], []
    for a,b,c,d in stage2:
        for e,f in product(range(45), repeat=2):
            positions = {0:a, 1:b, 2:c, 3:0, 4:d, 5:e, 6:f}
            row = [a,b,c,d,e,f]
            if not trace_is_admissible(45, 7, positions):
                continue
            after7.append(row)
            if not trace_is_admissible(45, 13, positions):
                continue
            after13.append(row)
            if trace_is_admissible(45, 19, positions):
                after19.append(row)
    assert after19 == []
    return {'normalized_token':3, 'stage1_tokens':[0,1,2], 'stage1_modulus':3,
            'stage1_normal_forms':stage1,
            'stage2_tokens':[0,1,2,4], 'stage2_modulus':5,
            'stage2_normal_forms':stage2,
            'final_tokens':[0,1,2,4,5,6], 'final_candidate_count':len(stage2)*45**2,
            'after_mod7_count':len(after7), 'after_mod13':after13,
            'after_mod19':after19}


def r55_certificates():
    # Normalize the sole factor 3 at zero.
    stage1 = [a for a in range(55)
              if trace_is_admissible(55, 5, {0:0, 3:a})]
    assert stage1 == [1,54]
    stage2 = [ab for ab in product(range(55), repeat=2)
              if trace_is_admissible(55, 11, {0:0, 1:ab[0], 2:ab[1]})]
    assert len(stage2) == 19
    after3, after13, after17 = [], [], []
    for a in stage1:
        for b,c in stage2:
            for d,e in product(range(55), repeat=2):
                positions = {0:0, 1:b, 2:c, 3:a, 4:d, 5:e}
                row = [b,c,a,d,e]
                if not trace_is_admissible(55, 3, positions):
                    continue
                after3.append(row)
                if not trace_is_admissible(55, 13, positions):
                    continue
                after13.append(row)
                if trace_is_admissible(55, 17, positions):
                    after17.append(row)
    assert len(after3) == 55 and after17 == []
    return {'normalized_token':0, 'stage1_tokens':[3], 'stage1_modulus':5,
            'stage1_normal_forms':stage1,
            'stage2_tokens':[1,2], 'stage2_modulus':11,
            'stage2_normal_forms':stage2,
            'final_tokens':[1,2,3,4,5],
            'final_candidate_count':len(stage1)*len(stage2)*55**2,
            'after_mod3':after3, 'after_mod13':after13, 'after_mod17':after17}


def r35_certificates():
    # Normalize the sole factor 3 at zero.
    stage1 = [a for a in range(35)
              if trace_is_admissible(35, 5, {0:0, 2:a})]
    assert stage1 == [1,34]
    stage2 = [abc for abc in product(range(35), repeat=3)
              if trace_is_admissible(35, 3, {0:0, 1:abc[0], 3:abc[1], 4:abc[2]})]
    expected = {(1,a,a) for a in range(35)} | {(a,1,a) for a in range(35)} | {(a,a,1) for a in range(35)}
    assert set(stage2) == expected and len(stage2) == 103
    after7, after11, after13 = [], [], []
    for a in stage1:
        for b,c,d in stage2:
            positions = {0:0, 1:b, 2:a, 3:c, 4:d}
            row = [b,a,c,d]
            if not trace_is_admissible(35, 7, positions):
                continue
            after7.append(row)
            if not trace_is_admissible(35, 11, positions):
                continue
            after11.append(row)
            if trace_is_admissible(35, 13, positions):
                after13.append(row)
    assert len(after7) == 114 and len(after11) == 4 and after13 == []
    return {'normalized_token':0, 'stage1_tokens':[2], 'stage1_modulus':5,
            'stage1_normal_forms':stage1,
            'stage2_tokens':[1,3,4], 'stage2_modulus':3,
            'stage2_normal_forms':stage2,
            'final_tokens':[1,2,3,4], 'final_candidate_count':206,
            'after_mod7_count':len(after7), 'after_mod11':after11, 'after_mod13':after13}


def r51_certificates():
    # Normalize the sole factor 43691 at zero.
    stage1 = [ab for ab in product(range(51), repeat=2)
              if trace_is_admissible(51, 3, {0:ab[0], 1:ab[1], 5:0})]
    assert stage1 == [(49,50),(50,49),(50,50)]
    stage2 = [(*ab,c,d) for ab in stage1 for c,d in product(range(51), repeat=2)
              if trace_is_admissible(51, 7, {0:ab[0], 1:ab[1], 2:c, 4:d, 5:0})]
    assert len(stage2) == 1085
    after5, after11, after13 = [], [], []
    for a,b,c,d in stage2:
        for e in range(51):
            positions = {0:a, 1:b, 2:c, 3:e, 4:d, 5:0}
            row = [a,b,c,e,d]
            if not trace_is_admissible(51, 5, positions):
                continue
            after5.append(row)
            if not trace_is_admissible(51, 11, positions):
                continue
            after11.append(row)
            if trace_is_admissible(51, 13, positions):
                after13.append(row)
    assert len(after11) == 2 and after13 == [], (len(after5), len(after11), after13)
    return {'normalized_token':5, 'stage1_tokens':[0,1], 'stage1_modulus':3,
            'stage1_normal_forms':stage1,
            'stage2_tokens':[0,1,2,4], 'stage2_modulus':7,
            'stage2_normal_forms':stage2,
            'final_tokens':[0,1,2,3,4], 'final_candidate_count':len(stage2)*51,
            'after_mod5_count':len(after5), 'after_mod11':after11, 'after_mod13':after13}


def tiny_certificates():
    result = {}
    for r, modulus, other_tokens in [(15,33,[1,2]), (21,3,[1]),
                                      (33,33,[1,3]), (39,3,[1]),
                                      (57,3,[1]), (63,3,[1,2])]:
        for places in product(range(r), repeat=len(other_tokens)):
            positions = {0:0, **dict(zip(other_tokens,places))}
            assert not trace_is_admissible(r, modulus, positions), (r, places)
        result[str(r)] = {'normalized_token':0, 'modulus':modulus,
                          'other_active_tokens':other_tokens,
                          'checked_position_count':r**len(other_tokens),
                          'all_excluded':True}
    return result


if __name__ == '__main__':
    start = perf_counter()
    assert all(prod(fs) == 2**r+1 for r,fs in FACTORS.items())
    result = {'direction':'2*p[next]+1 = d*p', 'factor_tokens':FACTORS,
              'tiny_cases':tiny_certificates()}
    for r, f in [(35,r35_certificates),(45,r45_certificates),
                 (51,r51_certificates),(55,r55_certificates)]:
        result[str(r)] = f()
        print(f'r={r}: staged checks passed', flush=True)
    output = Path(__file__).with_name('position_certificates.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'All ten counts verified in {perf_counter()-start:.3f}s; {output}', flush=True)
