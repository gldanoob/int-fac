"""Trace masses over F_{p²} and gcd-checked marked curves over a quadratic algebra."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path


mass = run_path(str(Path(__file__).with_name("untwisted-legendre-traces.py")))["mass"]
base = run_path(str(Path(__file__).with_name("moving-legendre.py")))
marks, character, primes_up_to = (base[key] for key in ("marks", "character", "primes_up_to"))


class Factor(Exception):
    pass


class BadModel(Exception):
    pass


class QuadraticRing:
    def __init__(self, n, h):
        self.n, self.h = n, h

    def add(self, u, v):
        return ((u[0] + v[0]) % self.n, (u[1] + v[1]) % self.n)

    def neg(self, u):
        return (-u[0] % self.n, -u[1] % self.n)

    def sub(self, u, v):
        return self.add(u, self.neg(v))

    def scale(self, u, k):
        return (u[0] * k % self.n, u[1] * k % self.n)

    def mul(self, u, v):
        a, b = u
        c, d = v
        return ((a * c + self.h * b * d) % self.n, (a * d + b * c) % self.n)

    def norm(self, u):
        return (u[0]**2 - self.h * u[1]**2) % self.n

    def is_unit(self, u):
        common = gcd(self.n, *u)
        norm_gcd = gcd(self.n, self.norm(u))
        for g, kind in ((common, "coefficients"), (norm_gcd, "norm")):
            if 1 < g < self.n:
                raise Factor(g, kind)
        if common == self.n:
            return False
        if norm_gcd == 1:
            return True
        raise BadModel("split zero divisor without a proper integer gcd")

    def inv(self, u):
        if not self.is_unit(u):
            raise BadModel("zero denominator")
        return self.scale((u[0], -u[1]), pow(self.norm(u), -1, self.n))


def add_points(ring, left, right, a2, a4):
    if left is None or right is None:
        return right if left is None else left
    x, y = left
    xx, yy = right
    diff = ring.sub(xx, x)
    if ring.is_unit(diff):
        numerator, denominator = ring.sub(yy, y), diff
    else:
        if not ring.is_unit(ring.add(y, yy)):
            return None
        assert not ring.is_unit(ring.sub(y, yy))
        numerator = ring.add(ring.mul(ring.add(ring.scale(x, 3), ring.scale(a2, 2)), x), a4)
        denominator = ring.scale(y, 2)
    slope = ring.mul(numerator, ring.inv(denominator))
    x3 = ring.sub(ring.sub(ring.sub(ring.mul(slope, slope), a2), x), xx)
    return x3, ring.sub(ring.mul(slope, ring.sub(x, x3)), y)


def marked(ring, lam, a, scalar):
    one = (1, 0)
    den = ring.inv((a.denominator, 0))
    aa = ring.scale(den, a.numerator)
    d = ring.mul(ring.mul(aa, ring.sub(aa, one)), ring.sub(aa, lam))
    for value in (lam, ring.sub(lam, one), d):
        if not ring.is_unit(value):
            raise BadModel("singular curve or zero twist")
    d2 = ring.mul(d, d)
    a2 = ring.neg(ring.mul(d, ring.add(one, lam)))
    a4 = ring.mul(d2, lam)
    pt, acc = (ring.mul(d, aa), d2), None
    for bit in bin(scalar)[2:]:
        acc = add_points(ring, acc, acc, a2, a4)
        if bit == "1":
            acc = add_points(ring, acc, pt, a2, a4)
    return acc


def traces(p, h):
    q = p * p
    # chi_{p²}(z) = chi_p(Norm(z)), and chi(x(x-1)(x-lambda)) factors.
    chi = [[character(x * x - h * y * y, p) for x in range(p)] for y in range(p)]
    constant = [[row[x] * row[x - 1] for x in range(p)] for row in chi]
    histogram = Counter()
    by_lambda = {}
    for y in range(p):
        for x in range(p):
            if y == 0 and x in (0, 1):
                continue
            t = -sum(constant[b][a] * chi[(b-y) % p][(a-x) % p]
                     for b in range(p) for a in range(p))
            by_lambda[x, y] = t
            histogram[t] += 1
    ordinary = 0
    for t in range(-2*p, 2*p+1):
        if t % p == 0 or (q + 1 - t) % 8 != 4:
            continue
        disc = t*t - 4*q
        assert histogram[t] == 2 * (mass(disc) - mass(disc//4)) >= mass(disc)
        ordinary += 1
    return by_lambda, ordinary


def odd_scalar(n):
    s = 1
    for prime in (3, 5, 7, 11, 13):
        power = prime
        while prime * power <= 4*n*n:
            power *= prime
        s *= power
    return s


def conic(f, count):
    return marks(Fraction((f+1)**2, (f-1)**2), count)


def check_mark_prefix(p, h):
    ring = QuadraticRing(p, h)
    checks = 0
    for f in (2, 3, 5):
        residues = []
        for a in conic(f, 12):
            if a.denominator % p:
                value = a.numerator * pow(a.denominator, -1, p) % p
                if value not in residues and value not in (0, 1):
                    residues.append(value)
        for length in range(1, min(len(residues), 6) + 1):
            signs = [tuple(character(ring.norm((a - x, -y)), p) for a in residues[:length])
                     for x in range(p) for y in range(p)]
            count = 2**length
            for target in product((-1, 1), repeat=length):
                misses = sum(all(v != t for v, t in zip(row, target)) for row in signs)
                assert count*misses <= p*p + ((length-2)*(count//2)+1)*p + length*count
                checks += 1
    return checks


def check_composite(p, h, hist):
    ring = QuadraticRing(p, h)
    passed = powers = 0
    found_by = Counter()
    for q in (17, 19, 23, 29, 31, 37, 41, 43):
        if p == q or character(h, q) != 1:
            continue
        root = next(x for x in range(1, q) if x*x % q == h % q)
        f = next(x for x in (2, 3, 5, 7, 11, 13) if character(x, q) == -1 and (x*x-1) % q != 0)
        for a in conic(f, 6):
            if gcd(a.denominator*a.numerator*(a.numerator-a.denominator), p*q) != 1:
                continue
            aa = a.numerator * pow(a.denominator, -1, p) % p
            checked_mark = False
            for (x, y), t in hist.items():
                n = p*p+1-t
                if y == 0 or abs(t) > p or n % 8 != 4 or odd_scalar(p*q) % (n//4):
                    continue
                if character(ring.norm((aa-x, -y)), p) != 1:
                    continue
                assert marked(ring, (x, y), a, n//4) is None
                # Check both embeddings at q by independent base-field affine arithmetic.
                clean = True
                xq = a.numerator * pow(a.denominator, -1, q) % q
                for sign in (-1, 1):
                    lam = (x + sign * y * root) % q
                    if lam in (0, 1, xq):
                        clean = False
                        break
                    assert base["marked_product"](a, lam, n//4, q) is not None
                if not clean:
                    continue
                for d in (p*q, p*p*q):
                    try:
                        marked(QuadraticRing(d, h), (x, y), a, n//4)
                    except Factor as hit:
                        assert 1 < hit.args[0] < d and d % hit.args[0] == 0
                        found_by[hit.args[1]] += 1
                        powers += d == p*p*q
                    else:
                        raise AssertionError((p, q, h, x, y, a))
                passed += 1
                checked_mark = True
                break
            if checked_mark:
                break
    return passed, powers, found_by


def blind(n):
    s = odd_scalar(n)
    for k in (2, 3, 4):
        for j in range(n.bit_length()):
            word, mask = n >> j, (1 << k)-1
            lam = (word & mask, (word >> k) & mask)
            for h in (2, 3, 5, 7):
                for f in (2, 3, 5, 7):
                    for a in conic(f, 2):
                        try:
                            marked(QuadraticRing(n, h), lam, a, s)
                        except Factor as hit:
                            return hit.args[0]
                        except BadModel:
                            continue
    return None


def square_counts():
    # For ordered odd smooth numbers the square-center Hasse test is exact.
    primes = primes_up_to(511)
    counted = occupied = 0
    for p in primes:
        if p < 5:
            continue
        supply = 0
        for m in range((p*p+1-p+3)//4, (p*p+1+p)//4+1):
            if m % 2 == 0:
                continue
            t = p*p+1-4*m
            assert t % p != 0
            n = m
            for s in (3, 5, 7, 11, 13):
                while n % s == 0:
                    n //= s
            supply += n == 1
        counted += 1
        occupied += supply > 0
    for start in (16, 64, 256):
        for width in (start, 2*start, 4*start):
            for end in range(start*start, 4*start*start, start):
                number = max(0, isqrt(end+width) - max(start-1, isqrt(end)))
                assert number <= width//(2*start) + 1
    return counted, occupied


def main():
    fields = params = ordinary = witnesses = powered = prefix_checks = 0
    found_by = Counter()
    for p in (5, 7, 11, 13, 17, 19, 23):
        h = next(x for x in (2, 3, 5, 7, 11, 13, 17) if character(x, p) == -1)
        hist, total = traces(p, h)
        prefix_checks += check_mark_prefix(p, h)
        fields += 1
        params += len(hist)
        ordinary += total
        local, rep, how = check_composite(p, h, hist)
        witnesses += local
        powered += rep
        found_by.update(how)
    for n in (35, 175):
        ring = QuadraticRing(n, 2)
        assert ring.norm((-15, 5)) == 0
        try:
            ring.is_unit((-15, 5))
        except Factor as hit:
            assert hit.args == (5, "coefficients")
        else:
            raise AssertionError("lost an inert factor")
    assert witnesses >= 5 and powered == witnesses
    samples = [11*17, 13*19, 17*23, 19*29, 23*31, 11**2*17, 13*19**2, 7*11*31]
    for n in samples:
        divisor = blind(n)
        assert divisor and 1 < divisor < n and n % divisor == 0
    print("square fields, Legendre parameters, ordinary trace formula checks", fields, params, ordinary)
    print("locally verified witnesses, repeated-prime inputs, gcd branches", witnesses, powered, found_by)
    print("integer-only splits, signed finite-field prefix estimates", len(samples), prefix_checks)
    print("square Hasse centers, occupied at cutoff 13", *square_counts())


if __name__ == "__main__":
    main()
