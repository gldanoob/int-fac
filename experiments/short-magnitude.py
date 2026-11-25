"""Recover two synthetic prime-power blocks using short Salié thresholds and PARI/GP."""

from cmath import exp
from fractions import Fraction
from math import atan2, ceil, cos, gcd, isqrt, pi, sin, sqrt
import os
import subprocess


def halved_phase(levels):
    phase = levels[-1]
    for target in reversed(levels[:-1]):
        phase = min((phase/2, (phase+1)/2),
                    key=lambda v: min((v-target) % 1, (target-v) % 1))
    return phase


def short_intervals(n, bit):
    """Generate centers without knowing a mixed root. Finite replay parameters."""
    window, mesh = 64, 1024
    bound = isqrt(n)//12
    shifts = [1 << j for j in range((bound//2).bit_length())]
    offsets = range(-window, window+1)
    weights = [(window+1-abs(k))/(window+1)**2 for k in offsets]
    centers = []

    def add(phase, radius, kind):
        for offset in (0, 1):
            centers.append([int(n*(phase+offset)//2), radius+1, kind])

    largest = 1
    while window*largest <= bound//2:
        anchor = [w*bit(k*largest) for k, w in zip(offsets, weights, strict=True)]
        peaks = []
        for tag in range(1, mesh):
            if min(tag, mesh-tag) < mesh//(window+1):
                continue
            z = exp(-2j*pi*tag/mesh)
            value = sum(v*z**k for k, v in zip(offsets, anchor, strict=True))
            peaks.append((abs(value), tag, value))
        for strength, tag, value in sorted(peaks, reverse=True)[:8]:
            if strength < .12:
                continue
            kernel = [w*exp(-2j*pi*k*tag/mesh) for k, w in zip(offsets, weights, strict=True)]
            levels = []
            for shift in shifts:
                row = sum(w*bit(k*largest+shift) for k, w in zip(offsets, kernel, strict=True))/value
                levels.append(Fraction(round(32*atan2(row.imag, row.real)/(2*pi)) % 32, 32))
            add(halved_phase(levels), ceil(Fraction(n, 16*shifts[-1])), 1)
        largest *= 2
    # Rolling through every small rational avoids testing the hidden dilation condition.
    last_dilation = largest//2
    max_denominator = 9
    epsilon = Fraction(1, 8*max_denominator**2)
    radius = ceil(n*epsilon/(2*last_dilation))
    for phase in sorted({Fraction(j, d) for d in range(1, max_denominator+1) for j in range(d)}):
        add(phase, radius, 2)
    return centers


def lattice_split(n, centers):
    source = r"""
findBlock(n,rows) = {
  my(B=max(1,sqrtint(n)\8),calls=0);
  foreach(rows,v,my(lo=v[1]-v[2],hi=v[1]+v[2]);
    forstep(left=lo,hi,2*B+1,
      my(c=left+B);calls++;
      foreach(zncoppersmith((x+c)^2-1,n,B),z,my(r=c+z);
        if(r<lo || r>hi || (r^2-1)%n,next);
        my(g=gcd(r-1,n));
        if(g>1 && g<n,return([g,v[3],calls])))));
  error("no mixed root in candidates")
};
"""
    source += f"iferr(print(findBlock({n},{centers})),E,print(E);quit(1));quit(0);\n"
    proc = subprocess.run([os.environ.get("GP", "gp"), "-fq"], input=source,
                          capture_output=True, text=True, check=True)
    return tuple(map(int, proc.stdout.strip().strip("[]").split(",")))


def check_fixture(u, v, policy):
    n = u*v
    root = 1 + u*((-2*pow(u, -1, v)) % v)
    answers = {}
    ambiguous = set()

    class Divisor(Exception):
        pass

    def answer(t):
        t = abs(t)
        assert 12*t <= isqrt(n)
        if not t:
            return 1
        d = gcd(t, n)
        if d != 1:
            raise Divisor(d)
        if t not in answers:
            w = 2*cos(4*pi*t/n) + 2*cos(2*pi*((2*t*root) % n)/n)
            bit = abs(w) > 1
            if abs(abs(w)-1) < 2**-12-1e-12:
                ambiguous.add(t)
                bit = (t.bit_count() % 2 == 0) if policy == "parity" else not bit
            answers[t] = bit
        return answers[t]

    if n % 3 == 0:
        factor, kind, calls = 3, "trial", 0
    else:
        try:
            factor, source, calls = lattice_split(n, short_intervals(n, answer))
            kind = ("", "phase", "rational")[source]
        except Divisor as exc:
            factor, kind, calls = exc.args[0], "gcd", 0
            while (shared := gcd(factor, n//factor)) > 1:
                factor *= shared
    assert factor in (u, v)
    print(n, policy, kind, factor, "unit calls", len(answers), "ambiguous", len(ambiguous),
          "maximum frequency", max(answers, default=0), "lattice calls", calls, flush=True)


def check_gaps():
    ordinary = exceptional = 0
    for n in range(145, 100001, 2):
        left, blocks, p = n, [], 3
        while p*p <= left:
            d = 1
            while left % p == 0:
                left //= p
                d *= p
            if d > 1:
                blocks.append(d)
            p += 2
        if left > 1:
            blocks.append(left)
        if len(blocks) != 2:
            continue
        u, v = blocks
        root = 1+u*((-2*pow(u, -1, v)) % v)
        for t in range(1, isqrt(n)//12+1):
            if gcd(t, n) != 1:
                continue
            a = (2*t*root) % n
            k = 3*min(a, n-a)-n
            w = 2*cos(4*pi*t/n)+2*cos(2*pi*a/n)
            gap = abs(abs(w)-1)
            assert (k*k-36*t*t) % n == 0
            if n % 3 == 0 and n % 9:
                y = 4*pi*t/n
                assert abs(k) == 6*t
                assert min(abs(w-cos(y)+s*sqrt(3)*sin(y)) for s in (-1, 1)) < 1e-12
                assert y-1e-12 <= gap <= 2*y+1e-12
                exceptional += 1
            else:
                assert k*k >= n+36*t*t and gap >= 1/sqrt(n)-1e-12
                assert (abs(w) > 1) == (k < 0)
                ordinary += 1
    print("short-frequency gap checks", ordinary, "exceptional modulus checks", exceptional)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O so replay checks are enabled")
    check_gaps()
    for u, v in ((1000003, 1000033), (1000037, 1000039), (1009**2, 1000003), (3, 1000003)):
        for policy in ("parity", "opposite"):
            check_fixture(u, v, policy)
