#!/usr/bin/env python3
"""Select four coefficients by exact conditional expectations on finite boxes."""

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import gcd, isqrt, prod
from pathlib import Path
from random import Random
from runpy import run_path

HERE = Path(__file__).resolve().parent
scalar = run_path(str(HERE / "cogentic-scalar-progression-sieve.py"))
primes_through, progression_sieve = scalar["primes_through"], scalar["progression_sieve"]


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


def hit_coset(hits):
    """Intersect congruences in a triangular lattice coset."""
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
            return None
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
    return x0, y0, P, R, Q


def box_count(box, coset):
    x0, y0, P, R, Q = coset
    x, y, p, q = box
    first = -((x0-x)//P)
    n = (x+p-1-x0)//P - first + 1
    bottom = y-1-y0-R*first
    return floor_sum(n, Q, -R, bottom+q) - floor_sum(n, Q, -R, bottom)


def signed_cosets(conditions):
    hits = tuple(test for test in conditions if test.equal)
    misses = tuple(test for test in conditions if not test.equal)
    for k in range(len(misses)+1):
        for extra in combinations(misses, k):
            coset = hit_coset(hits+extra)
            if coset is not None:
                yield (-1)**k, coset


def field_count(box, factor, band):
    """Count one field's passing pairs by Euclidean sums or scalar sections."""
    if not factor.smooth:
        return sum(sign*box_count(box, coset) for sign, coset in signed_cosets(factor.modular))

    first, *rest = sorted(set(factor.smooth), key=lambda test: test.mark)
    a = first.mark
    first_band = prod(p for p in band if p not in first.omit)
    if rest:
        second = rest[0]
        second_band = tuple(p for p in band if p not in second.omit)
        dy = second.step*(second.mark-a)
    transformed = tuple(Congruence(test.x, test.y-a*test.x, test.offset, test.modulus, test.equal)
                        for test in factor.modular)
    x, y, p, q = box
    x_end, y_end = x+p-1, y+q-1
    u_min, u_max = x+a*y, x_end+a*y_end

    def sections(coset):
        u0, y0, P, R, Q = coset
        total = 0
        for i in range(-((u0-u_min)//P), (u_max-u0)//P+1):
            u = u0+P*i
            value = first.offset+first.step*u
            if not value or first_band % abs(value):
                continue
            lo, hi = y, y_end
            if a:
                lo = max(lo, -((x_end-u)//a))
                hi = min(hi, (u-x)//a)
            start_y = lo+(y0+R*i-lo) % Q
            if start_y > hi:
                continue
            length = (hi-start_y)//Q+1
            if not rest:
                total += length
            else:
                start = second.offset+second.step*u+dy*start_y
                total += progression_sieve(start, dy*Q, length, second_band)[0]
        return total

    return sum(sign*sections(coset) for sign, coset in signed_cosets(transformed))


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


def check_mixed():
    rng = Random(20261127)
    band = (5, 7, 11, 13)
    empty = Factor()
    for _ in range(300):
        x, y = (rng.randrange(-9, 10) for _ in range(2))
        p, q = (rng.randrange(1, 11) for _ in range(2))
        marks = rng.sample(range(5), rng.randrange(1, 3))
        smooth = tuple(Smooth(a, rng.randrange(-9, 10), rng.randrange(-4, 5),
                              tuple(rng.sample(band, rng.randrange(len(band)+1)))) for a in marks)
        modular = tuple(Congruence(*(rng.randrange(-6, 7) for _ in range(3)),
                                   rng.randrange(1, 9), bool(rng.randrange(2)))
                        for _ in range(rng.randrange(4)))
        factor = Factor(smooth, modular)
        direct = sum(direct_score(band, (i, j, 0, 0), ((1, factor, empty),))
                     for i in range(x, x+p) for j in range(y, y+q))
        assert field_count((x, y, p, q), factor, band) == direct

    width, modulus = 1 << 1024, (1 << 2048)-1
    box = (0, 0, width, width)
    # The nonunit first hit fixes x+y=5. The second hit leaves y in {1,3,5}.
    # The second smooth values are then 3,7,11, and only 11 is accepted.
    modular = (Congruence(6, 6, -30, 6*modulus), Congruence(0, 4, -4, 8))
    factor = Factor((Smooth(1, 0, 1), Smooth(3, -4, 1, (7,))), modular)
    assert field_count(box, factor, band) == 1
    # A single accepted u=x+y=width-1 leaves the entire y interval.
    factor = Factor((Smooth(1, 6-width, 1),),
                    (Congruence(6, 6, -6*(width-1), 6*modulus),))
    assert field_count(box, factor, band) == width
    print("300 mixed boxes agree with enumeration, plus two large-period closed forms")


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
    check_mixed()
    check_cases()
