"""Numerical replay for the original-modulus Salié magnitude threshold. Requires NumPy."""

import argparse
from fractions import Fraction
from itertools import product
from math import ceil, cos, floor, fsum, gcd, isqrt, log, log1p, pi, prod, sqrt
from random import Random

import numpy as np


def known_progression(n):
    """Trial-divide small primes and freeze the known local phases by CRT."""
    m = n
    blocks = []
    for p in (3, 5, 7):
        d = 1
        while m % p == 0:
            m //= p
            d *= p
        if d > 1:
            blocks.append(d)
    k = n//m
    gain = t0 = 0
    for d in blocks:
        if d == 3 or gain <= 1.2:
            phase = (d-1)//2
        else:
            windows = [((d+5)//6, 2*d//9), ((5*d+17)//18, d//3)]
            phase = next(a for lo, hi in windows for a in range(lo, hi+1)
                         if gcd(a, d) == 1)
        gain += log(abs(2*cos(2*pi*phase/d)))
        # Local phase is 2 * (n/d)^(-1) * t / d.
        residue = phase*(n//d)*pow(2, -1, d) % d
        t0 = (t0 + residue*(k//d)*pow(k//d, -1, d)) % k
    assert -1e-10 <= gain <= 2
    return m, k, t0, tuple(blocks), gain


def is_prime(n):
    if n < 2 or any(n != p and n % p == 0 for p in (2, 3, 5, 7, 11, 13)):
        return False
    if n > 13 and any(pow(a, n-1, n) != 1 for a in (2, 3, 5)):
        return False
    return all(n % p for p in range(3, isqrt(n)+1, 2))


def prime_power(n):
    if is_prime(n):
        return True
    for e in range(2, n.bit_length()):
        lo, hi = 1, 1 << ((n.bit_length()+e-1)//e)
        while lo+1 < hi:
            mid = (lo+hi)//2
            if mid**e <= n:
                lo = mid
            else:
                hi = mid
        if lo**e == n and is_prime(lo):
            return True
    return False


def frequency(phases, modulus):
    levels = [Fraction(int(level) % 32, 32) for level in phases]
    phase = levels[-1]
    for target in reversed(levels[:-1]):
        phase = min((phase/2, (phase+1)/2),
                    key=lambda z: min((z-target) % 1, (target-z) % 1))
    return round(phase*modulus) % modulus


def recover(n, query, seed, half_window, limit, split=False):
    m, k, t0, known, gain = known_progression(n)
    if m == 1 or prime_power(m):
        return sorted([*known] + ([m] if m > 1 else [])), known, gain, 0, 0, []
    rng = Random(seed)
    js = [0]+[1 << j for j in range(m.bit_length()+1)]
    offsets = np.arange(-half_window, half_window+1)
    weight = (half_window+1-np.abs(offsets))/(half_window+1)**2
    mesh = 1 << (16*half_window-1).bit_length()
    returned = set()
    missing_samples = 0
    history = []

    def accept(d, attempt, source):
        if d <= 1 or m % d or gcd(d, m//d) != 1 or d in returned or not prime_power(d):
            return
        returned.add(d)
        history.append((attempt, d, source))

    for attempt in range(1, limit+1):
        a, s = rng.randrange(m), rng.randrange(m)
        bases = [(s+j*a) % m for j in range(-half_window, half_window+1)]
        rows = []
        for shift in js:
            locations = [(b+shift) % m for b in bases]
            good, samples = [], []
            for i, u in enumerate(locations):
                d = gcd(t0+k*u, n)
                if d == 1:
                    good.append(i)
                    samples.append(t0+k*u)
                else:
                    missing_samples += 1
                    if split:
                        while (shared := gcd(d, m//d)) > 1:
                            d *= shared
                        accept(d, attempt, "gcd")
            row = np.zeros(len(bases))
            row[good] = query(n, samples)
            rows.append(row*weight)

        # NumPy's anchor FFT counts k from 0; the shifted rows use the same origin.
        spectral = np.abs(np.fft.rfft(rows[0], n=mesh))
        peak = np.flatnonzero((spectral >= np.roll(spectral, 1))
                              & (spectral >= np.roll(spectral, -1)))
        peak = peak[(peak > 2*mesh//half_window) & (peak < mesh//2)]
        tags = sorted(peak, key=lambda t: spectral[t], reverse=True)[:32]
        tags = np.asarray([t for t in tags if spectral[t] > .015], dtype=float)
        matrix = np.asarray(rows)
        angles = (2*pi/mesh)*np.outer(np.arange(len(bases)), tags)
        sums = matrix @ np.cos(angles) - 1j * (matrix @ np.sin(angles))
        levels = np.rint(32*np.angle(sums[1:]/sums[0])/(2*pi)).astype(np.int64)
        for column in levels.T:
            f = frequency(column, m)
            accept(m//gcd(f, m), attempt, "phase")
        if prod(returned) == m:
            return sorted([*known, *returned]), known, gain, attempt, missing_samples, history
    raise AssertionError(("incomplete", n, seed, returned, missing_samples, history))


DELTA = 2**-12
SEED = 634921
FIXTURES = {
    "three": (10007, 10009, 10037**2),
    "five": (10007**2, 10009, 10037, 10039, 10061),
    "eight": (10007, 10009**2, 10037, 10039, 10061, 10067, 10069, 10079),
    "frozen-eight": (9, 25, 7, 10037**2, 10039, 10061, 10067, 10069),
    "twelve": (10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079,
               10091, 10093, 10099, 10103),
}


class SyntheticOracle:
    def __init__(self, blocks, mode):
        self.n = prod(blocks)
        self.blocks = blocks
        self.weights = [pow(self.n//d, -1, d) for d in blocks]
        self.mode = mode
        self.calls = self.gaps = self.changed = 0
        self.frozen = {d: None for d in blocks if gcd(d, 105) > 1}
        self.magnitudes = {}
        for d, c in zip(self.blocks, self.weights):
            if d <= 20000:
                residues = 2*c*np.arange(d, dtype=np.int64) % d
                self.magnitudes[d] = np.abs(2*np.cos(2*pi*residues/d))

    def magnitude(self, samples):
        values = np.ones(len(samples), dtype=float)
        for d, c in zip(self.blocks, self.weights):
            residues = np.fromiter((t % d for t in samples), np.int64, len(samples))
            if d in self.magnitudes:
                values *= self.magnitudes[d][residues]
            else:
                assert d <= 10**9  # keeps vectorized int64 modular products exact
                phases = ((2*c*residues) % d)/d
                values *= np.abs(2*np.cos(2*pi*phases))
        return values

    def query(self, modulus, samples):
        assert modulus == self.n and all(gcd(t, self.n) == 1 for t in samples)
        for d, residue in self.frozen.items():
            if samples and residue is None:
                residue = self.frozen[d] = samples[0] % d
            assert all(t % d == residue for t in samples)
        values = self.magnitude(samples)
        bits = values > 1
        # A small inward guard keeps binary64 rounding away from the allowed band edges.
        gap = np.flatnonzero(np.abs(values-1) <= DELTA-1e-9)
        if self.mode == "opposite":
            bits[gap] = ~bits[gap]
            self.changed += len(gap)
        elif self.mode == "alternating":
            replacement = (np.arange(self.gaps, self.gaps+len(gap)) % 2 == 0)
            self.changed += np.count_nonzero(bits[gap] != replacement)
            bits[gap] = replacement
        else:
            raise ValueError(self.mode)
        self.gaps += len(gap)
        self.calls += len(samples)
        return bits

    def check_root_sum(self):
        # Independent finite check of the product formula against the 2^R literal terms.
        roots = [sum(s*c*(self.n//d) for s, d, c in zip(signs, self.blocks, self.weights))
                 for signs in product((-1, 1), repeat=len(self.blocks))]
        samples = [t for t in (1, self.n//19, self.n//7+1) if gcd(t, self.n) == 1]
        for t, magnitude in zip(samples, self.magnitude(samples)):
            literal = fsum(cos(2*pi*((2*t*w) % self.n)/self.n) for w in roots)
            assert abs(abs(literal)-magnitude) < 1e-9


def check_density(bits):
    """Bracket convolution discretization error. FFT roundoff is not certified."""
    if not 12 <= bits <= 17:
        raise ValueError("use 12 through 17 grid bits")
    scale = 1 << bits
    bins = 16 * scale
    grid = np.arange(1, bins+1) / scale
    cdf = (2/pi) * np.arctan2(np.sqrt(-np.expm1(-2*grid)), np.exp(-grid))
    prior = np.diff(cdf, prepend=0)
    spectrum = np.fft.rfft(prior, n=2*bins)
    min_scaled, max_ratio, max_width = 1, 0, 0
    for r in range(2, 21):
        law = np.maximum(0, np.fft.irfft(np.fft.rfft(prior, n=2*bins)*spectrum)[:bins])
        cumulative = np.concatenate(([0], np.cumsum(law)))
        for index in range(17):
            w = r*log(2) + 2 - index/8
            last = floor(w*scale)
            starts = w - np.arange(last+1)/scale
            ends = np.maximum(0, starts-(r-1)/scale)

            def harmonic(z):
                return (2/pi)*np.exp(-z)*np.sqrt(-np.expm1(-2*z))

            left, right = harmonic(ends), harmonic(starts)
            lower = np.dot(prior[:last+1], np.minimum(left, right))
            peak = (ends <= log(2)/2) & (starts >= log(2)/2)
            upper = np.dot(prior[:last+1], np.where(peak, 1/pi, np.maximum(left, right)))
            band = (cumulative[1+floor((w-log1p(-DELTA))*scale)]
                    - cumulative[ceil((w-log1p(DELTA))*scale-r)])
            assert 0 < lower <= upper and 0 <= band < .01*lower
            min_scaled = min(min_scaled, sqrt(r)*lower)
            max_ratio = max(max_ratio, band/lower)
            max_width = max(max_width, upper-lower)
        prior = law
    print(f"{19*17} density cases, minimum scaled lower bound {min_scaled:.8g}, "
          f"maximum band ratio {max_ratio:.8g}, maximum bracket width {max_width:.8g}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("fixtures", nargs="*")
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--half-window", type=int, default=2048)
    parser.add_argument("--attempts", type=int, default=12)
    parser.add_argument("--split", action="store_true")
    parser.add_argument("--density", type=int, metavar="GRID_BITS")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without -O so replay checks are enabled")
    if args.density is not None:
        check_density(args.density)
        return
    for label in (args.fixtures or FIXTURES):
        blocks = FIXTURES[label]
        assert all(prime_power(d) for d in blocks)
        assert all(gcd(a, b) == 1 for i, a in enumerate(blocks) for b in blocks[:i])
        n = prod(blocks)
        for mode in ("opposite", "alternating"):
            oracle = SyntheticOracle(blocks, mode)
            oracle.check_root_sum()
            result, known, gain, attempt, missing, history = recover(
                n, oracle.query, args.seed, args.half_window, args.attempts, args.split)
            assert result == sorted(blocks)
            assert set(known) == oracle.frozen.keys()
            measured_gain = sum(log(oracle.magnitudes[d][r]) for d, r in oracle.frozen.items())
            assert abs(measured_gain-gain) < 1e-12
            print(label, mode, f"seed={args.seed}", f"n={n}", f"blocks={result}",
                  f"known={known}", f"gain={gain:.9f}", f"attempts={attempt}",
                  f"unit_calls={oracle.calls}", f"gap_replies={oracle.gaps}",
                  f"changed={oracle.changed}", f"nonunits={missing}", f"history={history}",
                  flush=True)


if __name__ == "__main__":
    main()
