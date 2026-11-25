"""Check the finite spectral bound for short-center advice on a fixed prime grid."""

from math import isqrt
import numpy as np


def primes_below(limit):
    sieve = bytearray([1]) * limit
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit-1)+1):
        if sieve[p]:
            sieve[p*p:limit:p] = bytes(len(sieve[p*p:limit:p]))
    return [p for p in range(2, limit) if sieve[p]]


def run():
    q = 65537
    size = q-1
    powers = np.array([pow(3, i, q) for i in range(size)])
    assert len(set(powers)) == size
    logs = np.zeros(q, dtype=int)
    logs[powers] = np.arange(size)
    truth = np.where(4*np.minimum(powers, q-powers) < q, 1, -1)
    spectrum = np.fft.fft(truth)
    spectral_peak_squared = np.max(np.abs(spectrum)**2)
    primes = [p for p in primes_below(q) if 2*p > q]
    positions = np.array([logs[2*pow(p, -1, q) % q] for p in primes])
    c = np.arange(1, 4097)
    length = len(c)
    best = np.full(len(primes), -length)
    for i in range(64):
        word = truth[(logs[c]+i*733) % size]
        weights = np.zeros(size)
        weights[logs[c]] = word
        values = np.fft.ifft(np.conj(np.fft.fft(weights))*spectrum).real
        scores = np.rint(values).astype(np.int64)
        assert np.max(np.abs(values-scores)) < 1e-7
        assert int(scores@scores) <= spectral_peak_squared*length + 1
        best = np.maximum(best, scores[positions])
        if i in (0, 3, 15, 63):
            print("table choices", i+1, "mean best accuracy",
                  round(float(.5+np.mean(best)/(2*length)), 6))
        for idx in (0, len(primes)//2, len(primes)-1):
            p = primes[idx]
            n = p*q
            r = 2*p*pow(p,-1,q)-1
            angles = np.array([(int(t)*r) % n for t in c])
            direct = np.where(4*np.minimum(angles, n-angles) < n, 1, -1)
            assert int(word@direct) == scores[positions[idx]]
    print("prime choices", len(primes), "centers", length,
          "direct table checks", 3*64, "full spectra", 64)


if __name__ == "__main__":
    run()
