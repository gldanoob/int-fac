"""Exact finite checks for the cube sampler, repeated prime slots and complete splits."""

from bisect import bisect_left, bisect_right
from collections import Counter
from functools import cache
from itertools import product
from math import isqrt, prod
from pathlib import Path
import runpy

ec = runpy.run_path(str(Path(__file__).with_name("moving-legendre.py")))


def binary_remainder(value, modulus):
    degree = modulus.bit_length() - 1
    while value.bit_length() > degree:
        value ^= modulus << (value.bit_length() - 1 - degree)
    return value


@cache
def field_modulus(degree):
    # Trial factors suffice for the small finite certificates here.
    for candidate in range((1 << degree) + 1, 1 << (degree + 1), 2):
        if all(binary_remainder(candidate, divisor) for r in range(1, degree // 2 + 1)
               for divisor in range(1 << r, 2 << r)):
            return candidate
    raise AssertionError("irreducible polynomial missing")


def field_mul(x, y, modulus):
    out = 0
    while y:
        if y & 1:
            out ^= x
        x <<= 1
        y >>= 1
    return binary_remainder(out, modulus)


@cache
def shifts(k, degree):
    field = 1 << degree
    modulus = field_modulus(degree)
    out = Counter()
    for u, v in product(range(field), repeat=2):
        state = v
        word = 0
        for i in range(k):
            word |= (state & 1) << i
            state = field_mul(state, u, modulus)
        out[word] += 1
    assert sum(out.values()) == field**2
    return out


def walsh(values):
    out = values[:]
    half = 1
    while half < len(out):
        for start in range(0, len(out), half * 2):
            for i in range(start, start + half):
                x, y = out[i], out[i + half]
                out[i], out[i + half] = x + y, x - y
        half *= 2
    return out


def check_sampler():
    spectra = sumsets = 0
    for k in range(2, 9):
        size = 1 << k
        for a in range(1, min(k, 5) + 1):
            field = 1 << a
            support = shifts(k, a)
            spectrum = walsh([support[i] for i in range(size)])
            powers = []
            for u in range(field):
                row = [1]
                for _ in range(1, k):
                    row.append(field_mul(row[-1], u, field_modulus(a)))
                powers.append(row)
            for char in range(1, size):
                roots = 0
                for row in powers:
                    total = 0
                    for i, value in enumerate(row):
                        if char >> i & 1:
                            total ^= value
                    roots += total == 0
                assert spectrum[char] == roots * field <= (k - 1) * field
                spectra += 1
            if a == k:
                assert len(support) == size
            targets = [{i for i in range(size) if i % r in (0, 2)} for r in (3, 7, 13)]
            targets.extend([{size - 2}, {1, 2}, {i for i in range(size) if i.bit_count() == k // 2}])
            bias = max(spectrum[1:])
            for target in targets:
                hit = {s ^ t for s in support for t in target}
                missed = size - len(hit)
                assert missed * len(target) * field**4 <= size * (size-len(target)) * bias**2
                sumsets += 1
    print("exact nontrivial character biases, target-set tail inequalities", spectra, sumsets)


def check_prime_slots():
    primes = ec["primes_up_to"](160000)
    rlist = [p for p in primes if 29 <= p <= 47]
    cofactors = [45, 55, 63, 75, 77, 81, 99, 105]
    cases = atoms = windows = occupied = 0
    for j in (2, 3):
        measure = Counter({m: 1 for m in cofactors})
        for _ in range(j):
            newer = Counter()
            for m, multiplicity in measure.items():
                for r in rlist:
                    newer[m * r] += multiplicity
            measure = newer
        literal = Counter(m * prod(word) for word in product(rlist, repeat=j) for m in cofactors)
        assert measure == literal
        for s, weight in measure.items():
            assert s % 2 and weight <= sum(s % r == 0 for r in rlist)**j
            remaining = s
            for p in primes:
                if p > 47:
                    break
                while remaining % p == 0:
                    remaining //= p
            assert remaining == 1
        orders = sorted(4 * s for s in measure)
        centers = list(primes[::67])
        for n in orders[::7]:
            p = n - 1
            while any(p % l == 0 for l in primes[:bisect_right(primes, isqrt(p))]):
                p += 2
            assert (n - p - 1)**2 <= p
            centers.append(p)
        for p in centers:
            lo, hi = p + 1 - isqrt(p), p + 1 + isqrt(p)
            count = bisect_right(orders, hi) - bisect_left(orders, lo)
            assert count == sum((n - p - 1)**2 <= p for n in orders)
            windows += 1
            occupied += bool(count)
        atoms += len(measure)
        cases += sum(measure.values())
    assert occupied > 60
    print("ordered tuples, distinct atoms, prime-centered windows, occupied", cases, atoms, windows, occupied)


def blind_split(n, stages=3):
    bits = n.bit_length()
    scalar = ec["odd_scalar"](n, 11)
    trial_marks = list(ec["marks"](2, 2)) + list(ec["marks"](3, 2))
    try:
        for a in range(1, stages + 1):
            for k in dict.fromkeys([(bits + 1) // 2, *range(1, bits + 1)]):
                cube_mask = (1 << k) - 1
                for j in range(bits):
                    start = n >> j & cube_mask
                    for shift in shifts(k, a):
                        lam = start ^ shift
                        if any(ec["checked_gcd"](v, n) != 1 for v in (lam, lam - 1)):
                            continue
                        for mark in trial_marks:
                            ec["marked_product"](mark, lam, scalar, n)
    except ec["ProperFactor"] as found:
        factor = found.args[0]
        assert 1 < factor < n and n % factor == 0
        return factor, a
    return None, 0


def check_costs():
    # A singleton puts the tail through several stages at these word lengths.
    k, p, cofactor = 8, 173, 23
    j = (p * cofactor).bit_length() - 1
    remaining = set(range(257, 513))
    hist = []
    target = {151}
    for a in range(1, 6):
        hit = {s ^ t for s in shifts(k, a) for t in target}
        solved = {q for q in remaining if (p * cofactor * q >> j) % (1 << k) in hit}
        remaining -= solved
        hist.append(len(solved))
    assert hist[0] > 0 and sum(hist[2:]) > 0
    assert sum(hist) + len(remaining) == 256
    print("partners hitting singleton by stage, remaining", hist, len(remaining))
    roots = ec["primes_up_to"](181)
    fixtures = [p * q for i, p in enumerate(roots) if 47 < p < 130 for q in roots[i+1:]]
    fixtures += [53**2 * 71, 59 * 67 * 151, 101*103**2*107, 79**2*109**2]
    fallback = fast = 0
    for n in fixtures:
        pending, output = [n], []
        while pending:
            d = pending.pop()
            if ec["toy_prime"](d):
                output.append(d)
                continue
            f, stage = blind_split(d)
            if f is None:
                fallback += 1
                f = next(r for r in range(2, isqrt(d) + 1) if d % r == 0)
            else:
                fast += 1
            pending.extend((f, d // f))
        assert prod(output) == n and all(ec["toy_prime"](p) for p in output)
    print("complete integer-only factorizations, elliptic/gcd splits, toy fallbacks",
          len(fixtures), fast, fallback)


if __name__ == "__main__":
    check_sampler()
    check_prime_slots()
    check_costs()
