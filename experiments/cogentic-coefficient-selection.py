#!/usr/bin/env python3
"""Select four coefficients by exact conditional expectations on finite boxes."""

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import gcd, isqrt, lcm, prod
from pathlib import Path
from random import Random
from runpy import run_path

HERE = Path(__file__).resolve().parent
scalar = run_path(str(HERE / "cogentic-scalar-progression-sieve.py"))
geometry = run_path(str(HERE / "cogentic-scalar-divisor-count.py"))
primes_through, progression_sieve = scalar["primes_through"], scalar["progression_sieve"]
panels, in_class = geometry["panels"], geometry["in_class"]


@dataclass(frozen=True)
class Smooth:
    mark: int
    offset: int
    step: int
    omit: tuple = ()


@dataclass(frozen=True)
class Congruence:
    x: int
    y: int
    offset: int
    modulus: int
    equal: bool = True

    def accepts(self, x, y):
        return ((self.offset + self.x*x + self.y*y) % self.modulus == 0) == self.equal


@dataclass(frozen=True)
class Factor:
    smooth: tuple = ()
    modular: tuple = ()

    def __post_init__(self):
        marks = {test.mark for test in self.smooth}
        if len(marks) > 2 or any(mark < 0 for mark in marks):
            raise ValueError("a factor needs at most two nonnegative smooth marks")
        if len(set(self.smooth)) != len(marks):
            raise ValueError("each mark must have a single smooth test")
        if any(test.modulus <= 0 for test in self.modular):
            raise ValueError("modulus must be positive")


def floor_sum(n, m, a, b):
    """Sum floor((a*i+b)/m) for 0 <= i < n, with signed a and b."""
    total = 0
    while True:
        qa, a = divmod(a, m)
        qb, b = divmod(b, m)
        total += qa*n*(n-1)//2 + qb*n
        top = a*n+b
        if top < m:
            return total
        n, b = divmod(top, m)
        m, a = a, m


def hit_count(box, hits):
    """Intersect congruences in a triangular lattice coset and clip to the box."""
    x0, y0, P, R, Q = 0, 0, 1, 0, 1
    for test in hits:
        # On (x0 + P*i, y0 + R*i + Q*j), the new constraint is a*i + b*j + c.
        m = test.modulus
        a = test.x*P + test.y*R
        b = test.y*Q
        c = test.offset + test.x*x0 + test.y*y0
        g = gcd(b, m)
        h = gcd(a, g)
        if c % h:
            return 0
        stride_i, stride_j = g//h, m//g
        i0 = (-c//h * pow(a//h, -1, stride_i)) % stride_i
        inverse = pow(b//g, -1, stride_j)
        j0 = (-(a*i0+c)//g * inverse) % stride_j
        slope_j = (-a*stride_i//g * inverse) % stride_j
        x0 += P*i0
        P *= stride_i
        y0 += R*i0 + Q*j0
        R = R*stride_i + Q*slope_j
        Q *= stride_j
        y0 %= Q
        R %= Q

    x, y, p, q = box
    first = -((x0-x)//P)
    n = (x+p-1-x0)//P - first + 1
    bottom = y-1-y0-R*first
    return floor_sum(n, Q, -R, bottom+q) - floor_sum(n, Q, -R, bottom)


def modular_count(box, conditions):
    hits = tuple(test for test in conditions if test.equal)
    misses = tuple(test for test in conditions if not test.equal)
    return sum((-1)**k * hit_count(box, hits+extra) for k in range(len(misses)+1)
               for extra in combinations(misses, k))


def field_count(box, factor, band):
    """Count one field's passing pairs by lattice or scalar projection."""
    if not factor.smooth:
        return modular_count(box, factor.modular)

    tests = {test.mark: (test, tuple(p for p in band if p not in test.omit))
             for test in factor.smooth}
    marks = set(tests)
    for extra in (0, 1):
        if len(marks) < 2:
            marks.add(extra)
    a, b = sorted(marks)
    delta = b-a
    period = delta*lcm(*(condition.modulus for condition in factor.modular))
    residues = []
    for u0 in range(period):
        allowed = []
        for v0 in range(u0 % delta, period, delta):
            y = (v0-u0)//delta
            if all(test.accepts(u0-a*y, y) for test in factor.modular):
                allowed.append(v0)
        if allowed:
            residues.append((u0, allowed))

    def count(mark, indices):
        if not indices or mark not in tests:
            return len(indices)
        test, primes = tests[mark]
        return progression_sieve(test.offset + test.step*indices.start,
                                 test.step*indices.step, len(indices), primes)[0]

    total = 0
    # shortcut: singleton panels for exact geometry, use certified wider panels to reduce scalar calls.
    for lo, hi, vlo, vhi, _, _ in panels(*box, a, b, 1):
        for u0, allowed in residues:
            left = count(a, in_class(lo, hi, u0, period))
            if left:
                total += left*sum(count(b, in_class(vlo, vhi, v0, period)) for v0 in allowed)
    return total


def select(B, box, terms):
    """Return the selected tuple, its direct score and the exact child means."""
    box = tuple(map(tuple, box))
    terms = tuple(terms)
    if B < 2 or len(box) != 2 or any(len(field) != 4 for field in box) or any(
        length <= 0 or length & (length-1) for field in box for length in field[2:]
    ):
        raise ValueError("need B >= 2 and two field boxes with power-of-two widths")
    if any(not isinstance(weight, (int, Fraction)) for weight, _, _ in terms):
        raise TypeError("exact score weights must be integers or fractions")
    band = ()
    if any(first.smooth or second.smooth for _, first, second in terms):
        band = tuple(p for p in primes_through(B) if p > isqrt(B))

    @cache
    def average(field, factor):
        return Fraction(field_count(field, factor, band), field[2]*field[3])

    def mean(prefix):
        return sum((weight*average(prefix[0], first)*average(prefix[1], second)
                    for weight, first, second in terms), Fraction(0))

    trace = []
    for side in (0, 1):
        while max(box[side][2:]) > 1:
            field = list(box[side])
            coord = int(field[3] > field[2])
            field[coord+2] //= 2
            left = box[:side] + (tuple(field),) + box[side+1:]
            field[coord] += field[coord+2]
            right = box[:side] + (tuple(field),) + box[side+1:]
            left_mean, right_mean = mean(left), mean(right)
            trace.append((left, right, left_mean, right_mean))
            box = left if left_mean <= right_mean else right

    point = box[0][:2] + box[1][:2]
    score = direct_score(band, point, terms)
    if score != mean(box):
        raise RuntimeError("direct leaf score disagrees with the projected count")
    return point, score, trace


def direct_score(band, point, terms):
    def accepts(factor, x, y):
        for test in factor.smooth:
            value = test.offset + test.step*(x + test.mark*y)
            if not value or prod(p for p in band if p not in test.omit) % abs(value):
                return False
        return all(test.accepts(x, y) for test in factor.modular)

    x, y, z, w = point
    return sum(weight for weight, first, second in terms
               if accepts(first, x, y) and accepts(second, z, w))


def check_modular():
    rng = Random(20261126)
    fixtures = [
        ((-5, -9, 14, 11), (Congruence(6, -4, -2, 8), Congruence(-3, 2, 1, 6))),
        ((-3, -2, 11, 9), (Congruence(2, 4, 1, 6),)),
        ((-3, -2, 11, 9), (Congruence(0, 0, 19, 1, False),)),
        ((-3, -2, 11, 9), (Congruence(1, 0, 0, 2), Congruence(1, 0, 1, 2))),
    ]
    for _ in range(300):
        box = tuple(rng.randrange(-12, 13) for _ in range(2)) + tuple(
            rng.randrange(1, 13) for _ in range(2))
        conditions = tuple(Congruence(*(rng.randrange(-12, 13) for _ in range(3)),
                                      rng.randrange(1, 14), bool(rng.randrange(2)))
                           for _ in range(rng.randrange(6)))
        fixtures.append((box, conditions))
    for (x, y, p, q), conditions in fixtures:
        direct = sum(all(test.accepts(i, j) for test in conditions)
                     for i in range(x, x+p) for j in range(y, y+q))
        assert field_count((x, y, p, q), Factor(modular=conditions), ()) == direct

    width, modulus = 1 << 2048, (1 << 521)-1
    d, r = divmod(width, modulus)
    box = (-width, -width, width, width)
    equal = r*(d+1)**2 + (modulus-r)*d**2
    assert field_count(box, Factor(modular=(Congruence(1, -1, 0, modulus),)), ()) == equal
    assert field_count(box, Factor(modular=(Congruence(1, -1, 0, modulus, False),)), ()) == width**2-equal
    # The band bound is irrelevant when the entire score consists of modular terms.
    term = (1, Factor(modular=(Congruence(1, -1, 0, modulus),)), Factor())
    _, score, trace = select(width, ((0, 0, 1 << 64, 1 << 64), (0, 0, 1, 1)), (term,))
    assert score == 0 and len(trace) == 128
    print(f"{len(fixtures)} modular boxes agree with enumeration, plus a 2049-bit closed-form box")


def check_cases():
    const = Factor()
    pair = Factor((Smooth(0, -1, 1, (5,)), Smooth(2, 10, -1, (7,))),
                  (Congruence(1, 1, 0, 4, False),))
    single = Factor((Smooth(3, 1, -2),), (Congruence(2, 1, 0, 3),))
    modular = Factor(modular=(Congruence(1, -2, 1, 4), Congruence(0, 1, 1, 2, False)))
    repeated = Factor((Smooth(1, 1, 0),)*2)
    terms = ((Fraction(7, 8), const, const), (-3, pair, single), (2, single, pair),
             (Fraction(-5, 4), modular, pair), (1, single, modular),
             (Fraction(-1, 4), repeated, modular))
    band = tuple(p for p in primes_through(13) if p > isqrt(13))

    def brute_mean(box):
        ranges = [range(start, start+length) for x, y, p, q in box
                  for start, length in ((x, p), (y, q))]
        return Fraction(sum(direct_score(band, pt, terms) for pt in product(*ranges)),
                        prod(map(len, ranges)))

    strict = 0
    for box in (((-4, -2, 16, 4), (-6, -2, 16, 8)),
                ((-6, -2, 8, 8), (-4, -2, 16, 4)),
                ((-6, -1, 16, 1), (-2, -4, 4, 16)),
                ((0, 0, 1, 1), (0, 0, 1, 1))):
        point, score, trace = select(13, box, terms)
        root = previous = brute_mean(box)
        for left, right, lm, rm in trace:
            assert (lm, rm) == (brute_mean(left), brute_mean(right))
            assert previous == (lm+rm)/2
            strict += lm != rm
            previous = min(lm, rm)
        assert score == previous <= root
        assert len(trace) == sum(length.bit_length()-1 for field in box for length in field[2:])
        assert all(start <= val < start+length for val, start, length in
                   zip(point, box[0][:2]+box[1][:2], box[0][2:]+box[1][2:]))
        print(f"{len(trace)} decisions, root {root}, selected {point} with score {score}")
    assert strict > 0


if __name__ == "__main__":
    check_modular()
    check_cases()
