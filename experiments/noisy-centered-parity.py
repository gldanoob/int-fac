"""Finite list decoding of corrupted short centered parities, with actual lattice calls."""

from fractions import Fraction
from importlib import import_module
from math import ceil, gcd, isqrt

import numpy as np

lattice_split = import_module("short-magnitude").lattice_split


def noisy_word(p, q, length):
    n = p * q
    root = 1 + p * ((-2 * pow(p, -1, q)) % q)
    angle = np.fromiter(((c*root) % n for c in range(1, length+1)), np.int64)
    unit = np.fromiter((gcd(c, n) == 1 for c in range(1, length+1)), bool)

    def sign(v):
        return np.where(4*np.minimum(v, n-v) < n, 1, -1)

    truth = sign(angle)
    # This fixed error pattern cancels the fundamental on a uniform circle.
    prediction = -sign(3*angle % n)
    return np.where(unit, prediction, 0), np.mean(truth[unit] == prediction[unit]), root


def learn(word, period, cutoff, seed):
    """Estimate Fourier mass in dyadic residue classes from random pair samples."""
    rng = np.random.default_rng(seed)
    signal = np.zeros(period)
    signal[1:len(word)+1] = word
    prefixes = np.array([0])
    size = 1
    while size < period:
        prefixes = np.concatenate([prefixes, prefixes+size])
        size *= 2
        count = 170_000
        x = rng.integers(period, size=count)
        k = rng.integers(size, size=count)
        products = signal[x] * signal[(x+k*(period//size)) % period]
        # All children at a level can share the same queries.
        totals = np.bincount(k, weights=products, minlength=size)
        estimates = np.fft.fft(totals).real / count
        prefixes = prefixes[estimates[prefixes] > cutoff]
        assert 0 < len(prefixes) <= 4/cutoff
    return sorted(prefixes, key=lambda f: -estimates[f])


def check(p, q):
    n = p*q
    length = isqrt(n)//6
    word, accuracy, root = noisy_word(p, q, length)
    period = 1 << (2*length).bit_length()
    assert .64 < accuracy < .69
    modes = learn(word, period, .004, 20261125)
    target = round(Fraction((3*root % n)*period, n)) % period
    first = round(Fraction(root*period, n)) % period
    assert target in modes and first not in modes and -first % period not in modes
    candidates = []
    for f in modes:
        for harmonic in (1, 2, 3, 4, 5):
            for j in range(harmonic):
                center = Fraction(n*(int(f)+j*period), period*harmonic)
                radius = ceil(Fraction(n, 2*period*harmonic)) + 1
                candidates.append([round(center), radius, 1])
    factor, _, calls = lattice_split(n, candidates)
    assert factor in (p, q)
    print("noisy short word", n, "T", length, "agreement", round(accuracy, 5),
          "listed", len(modes), "harmonic", 3, "factor", factor, "lattice calls", calls)


def check_literal():
    p, q = 11, 17
    n, radius, length = p*q, p*q//4, 13
    word, _, root = noisy_word(p, q, length)
    a, den = length**2*n, length**2*n**2+1
    cases = 0
    for c in range(1, length+1):
        if gcd(c, n) != 1:
            assert word[c-1] == 0
            continue
        center = length*n*c
        parity = (sum(a*x*x//den for x in range(center-radius, center+radius+1))
                  - a*center*center//den) % 2
        mixed = c*root % n
        assert (parity ^ (min(c, n-c) <= radius)) == (min(mixed, n-mixed) <= radius)
        cases += 1
    print("literal centered sums", cases)


if __name__ == "__main__":
    check_literal()
    check(10007, 17239)
    check(20011, 35221)
    p, q = 1000037, 1000039
    n = p*q
    length = isqrt(n)//12
    # The near-zero candidate applies even when the predictor is constant.
    factor, _, calls = lattice_split(n, [[0, ceil(Fraction(n, length)), 2]])
    assert factor in (p, q)
    print("small rational case", n, "factor", factor, "lattice calls", calls)
