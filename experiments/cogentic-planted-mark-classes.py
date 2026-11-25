"""Exact quotient distributions after planting f(0)=Y and prescribing a second root."""

from collections import Counter, defaultdict
from itertools import permutations, product
from math import gcd


def p_part(n, p):
    part = 1
    while n % (part*p) == 0:
        part *= p
    return part


def local_pairs(p):
    cases = {}
    for z, zz in permutations(range(2, p*p + p + 4), 2):
        key = (min(z % p, 3), min(zz % p, 3), gcd(z, p*p), gcd(zz, p*p),
               gcd(z-1, p*p), gcd(zz-1, p*p), gcd(z-zz, p*p))
        cases.setdefault(key, (z, zz))
    return cases.values()


def check_case(p, plant, root, z, zz):
    # f(X)=Y+X+X(X-1)(s+tX), with anchor 0 and common evaluation point 1.
    modulus = p*p
    y0 = p if plant else 1
    pre = lambda a: p if (plant and a % p == 0) or (root and a % p == 2) else 1
    p1, p2 = pre(z), pre(zz)
    d1, d2 = p_part(z*(z-1), p), p_part(zz*(zz-1), p)
    P1 = p if plant and z % p == 0 else 1
    P2 = p if plant and zz % p == 0 else 1
    both = p if root and z % p == zz % p == 2 else 1
    free = p if root and z % p != 2 and zz % p != 2 else 1
    period1, period2 = modulus*d1 // p1, modulus*d2 // p2
    step1 = d1 // P1
    step2 = gcd(period2, d2*p_part(z-zz, p)*free // (P2*both))
    at1 = Counter()
    fibers = defaultdict(Counter)
    for s, t in product(range(modulus), repeat=2):
        if root and (y0 + 2 + 2*(s + 2*t)) % p:
            continue
        x, xx = (s + z*t) % modulus, (s + zz*t) % modulus
        f, ff = y0 + z + z*(z-1)*x, y0 + zz + zz*(zz-1)*xx
        assert f % p1 == ff % p2 == 0
        at1[f // p1 % period1] += 1
        fibers[x][ff // p2 % period2] += 1
        if plant and gcd(z, modulus) == gcd(zz, modulus) == p:
            assert (ff//p - 1) % p == (zz//p)*pow(z//p, -1, p)*(f//p - 1) % p

    def check_law(counts, period, step):
        residue = next(iter(counts)) % step
        assert set(counts) == set(range(residue, period, step))
        assert len(set(counts.values())) == 1

    check_law(at1, period1, step1)
    for counts in fibers.values():
        check_law(counts, period2, step2)
    return len(fibers), sum(map(len, fibers.values()))


if __name__ == '__main__':
    systems = fibers = values = 0
    for p in (3, 5, 7):
        for z, zz in local_pairs(p):
            for plant, root in product((False, True), repeat=2):
                count, size = check_case(p, plant, root, z, zz)
                systems += 1
                fibers += count
                values += size
    print('planted local systems, first fibers, distinct second values:', systems, fibers, values)
