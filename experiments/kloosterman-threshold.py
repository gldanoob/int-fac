"""Finite bit-only Kloosterman factoring replays. Uses only the standard library."""

import cmath
import math
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from time import perf_counter

PADDING = (101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157)


def character(numerator, modulus):
    return cmath.exp(1j * math.tau * ((numerator % modulus) / modulus))


def fft(values):
    if len(values) == 1:
        return values
    even = fft(values[::2])
    odd = fft(values[1::2])
    terms = [character(-k, len(values)) * value for k, value in enumerate(odd)]
    return [a + b for a, b in zip(even, terms)] + [a - b for a, b in zip(even, terms)]


def distance(a, b):
    difference = (a - b) % 1
    return min(difference, 1 - difference)


def prime_base(block):
    """Trial division validates proposed blocks in these small fixtures."""
    if block < 2:
        return None
    for p in range(2, math.isqrt(block) + 1):
        if block % p == 0:
            while block % p == 0:
                block //= p
            return p if block == 1 else None
    return block


def filtered_frequencies(n, window, sample, cutoff):
    """A public dilation and FFT peaks shorten the exhaustive search in the proof."""
    q = n * n
    dilation = int.from_bytes(sha256(str(n).encode()).digest(), "big") % q
    assert math.gcd(dilation, n) == 1
    shifts = [0] + [1 << j for j in range(q.bit_length() + 1)]
    support = range(-window, window + 1)
    weights = [(window + 1 - abs(k)) / (window + 1)**2 for k in support]
    rows = []
    for shift in shifts:
        row = []
        for k, weight in zip(support, weights):
            t = (k * dilation + shift) % q
            row.append(weight * sample(t) if math.gcd(t, n) == 1 else 0)
        rows.append(row)

    grid_size = 16 * (window + 1)
    grid = [0] * grid_size
    for k, value in zip(support, rows[0]):
        grid[k % grid_size] = value
    magnitudes = list(map(abs, fft(grid)))
    frequencies = set()
    for x, value in enumerate(magnitudes):
        if value <= cutoff or value < magnitudes[x - 1] or value <= magnitudes[(x + 1) % grid_size]:
            continue
        phases = [character(-k * x, grid_size) for k in support]
        estimates = [sum(v * w for v, w in zip(row, phases)) for row in rows]
        angles = [Fraction.from_float(cmath.phase(v / estimates[0]) / math.tau) % 1
                  for v in estimates[1:]]
        lift = angles[-1]
        for observed in reversed(angles[:-1]):
            lift = min((lift / 2, (lift + 1) / 2), key=lambda v: distance(v, observed))
        frequencies.add(round(q * lift) % q)
    return frequencies


def threshold_lifts(padding):
    modulus = math.prod(padding)**2
    lifts = []
    for j in range(-40, 25):
        threshold = j / 8
        target = math.exp(-threshold / len(padding))
        residue, gain = 0, 1
        for p in padding:
            d = p * p
            u = round(d * math.acos(target / 2) / math.tau)
            if u % p == 0:
                u += 1
            gain *= 2 * math.cos(math.tau * u / d)
            residue += (modulus // d) * (u * pow(2, -1, d) % d)
        assert abs(math.log(gain) + threshold) < 1 / 80
        lifts.append((threshold, residue % modulus))
    assert len({v for _, v in lifts}) == len(lifts)
    return modulus, lifts


def threshold_decode(n, oracle, window):
    q = n * n
    padding, lifts = threshold_lifts(PADDING)
    assert math.gcd(padding, n) == 1

    @lru_cache(None)
    def sample(t):
        best = -5
        for threshold, v in lifts:
            reply = oracle((t * padding + v * q) % (q * padding))
            assert type(reply) is bool
            if reply:
                best = threshold
        return best + 1 / 16

    frequencies = filtered_frequencies(n, window, sample, 0.28)
    blocks = set()
    for f in frequencies:
        denominator = q // math.gcd(f, q)
        block = math.isqrt(denominator)
        if block * block == denominator and n % block == 0:
            p = prime_base(block)
            if p and (n // block) % p:
                blocks.add(block)
    assert math.prod(blocks) == n
    return sorted(blocks), frequencies, len(lifts) * sample.cache_info().misses


def quarter_sign(t, squares, inverses):
    value = 1
    for d, inverse in zip(squares, inverses):
        residue = (2 * t * inverse) % d
        if 4 * min(residue, d - residue) > d:
            value = -value
    return value


def sign_fixture(powers, window):
    n = math.prod(powers)
    q = n * n
    squares = [p * p for p in powers]
    inverses = [pow(q // d, -1, d) for d in squares]

    @lru_cache(None)
    def oracle(t):
        assert math.gcd(t, n) == 1
        return quarter_sign(t, squares, inverses)

    frequencies = filtered_frequencies(n, window, oracle, 0.1)
    halves = {f * pow(2, -1, q) % q for f in frequencies}
    roots = {w for w in halves if w * w % q == 1}
    assert len(roots) == 2**len(powers)
    blocks = [n]
    for w in roots:
        split = []
        for block in blocks:
            divisor = math.gcd(w - 1, block)
            split.extend(v for v in (divisor, block // divisor) if v > 1)
        blocks = split
    assert sorted(blocks) == sorted(powers)
    print(f"unpadded sign {n=} blocks={sorted(blocks)} roots={len(roots)} "
          f"queries={oracle.cache_info().misses}")


def direct_check():
    def direct(n, frequency):
        q = n * n
        return sum(character(frequency * (u + pow(u, -1, q)), q)
                   for u in range(1, q) if math.gcd(u, n) == 1) / n

    outcomes = set()
    for v in (1, 2, 3, 8):
        n, pad = 35, 3
        frequency = (v * pad**2 + pow(2, -1, pad**2) * n**2) % (n * pad)**2
        assert math.gcd(frequency, n * pad) == 1
        full = direct(n * pad, frequency)
        transferred = direct(n, v) * 2 * math.cos(math.tau / pad**2)
        assert abs(full - transferred) < 1e-10 and abs(abs(full) - 1) > 1 / 4096
        outcomes.add(abs(full) > 1)
    assert outcomes == {False, True}
    squares = (9, 25, 49)
    inverses = [pow(105**2 // d, -1, d) for d in squares]
    signs = set()
    for t in (1, 2, 4, 8, 11, 109):
        value = direct(105, t)
        result = quarter_sign(t, squares, inverses)
        assert abs(value.imag) < 1e-10 and result * value.real > 1e-8
        signs.add(result)
    assert signs == {-1, 1}


def threshold_fixture(powers, window):
    n = math.prod(powers)
    q, padding = n**2, math.prod(PADDING)**2
    pinv, qinv = pow(padding, -1, q), pow(q, -1, padding)

    def magnitude(frequency, blocks, modulus):
        result = 1
        for block in blocks:
            d = block * block
            angle = 2 * frequency * pow(modulus // d, -1, d)
            result *= 2 * character(angle, d).real
        return abs(result)

    @lru_cache(None)
    def local(t):
        return magnitude(t, powers, q)

    @lru_cache(None)
    def gain(v):
        assert math.gcd(v, padding) == 1
        return magnitude(v, PADDING, padding)

    calls = ambiguous = 0

    def oracle(frequency):
        nonlocal calls, ambiguous
        calls += 1
        t, v = frequency * pinv % q, frequency * qinv % padding
        assert math.gcd(t, n) == 1
        value = local(t) * gain(v)
        if abs(value - 1) <= 1 / 4096:
            ambiguous += 1
            return bool(frequency & 1)
        return value > 1

    start = perf_counter()
    blocks, frequencies, expected_calls = threshold_decode(n, oracle, window)
    assert blocks == sorted(powers) and calls == expected_calls
    fundamental = {sign * 4 * (q // p**2) * pow(q // p**2, -1, p**2) % q
                   for p in powers for sign in (-1, 1)}
    assert fundamental <= frequencies
    print(f"threshold {n=} {blocks=} queries={calls} gap_replies={ambiguous} "
          f"seconds={perf_counter() - start:.2f}")


if __name__ == "__main__":
    direct_check()
    sign_fixture((2053, 2063, 2081), 511)
    sign_fixture((2053, 2063, 2081, 2083), 511)
    sign_fixture((2053**2, 2063, 2081), 511)
    threshold_fixture((1009, 1013, 1019), 255)
    threshold_fixture((307**2, 1013, 1019), 255)
    threshold_fixture((1009, 1013, 1019, 1021), 255)
