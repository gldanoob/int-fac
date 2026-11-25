"""Compare direct modular collisions with the divisor test on each square block."""
from itertools import combinations_with_replacement
from math import gcd, isqrt, prod


def labels(height):
    return [(a, b) for a in range(1, height + 1)
            for b in range(-height, height + 1) if b and gcd(a, b) == 1]


def products(m, marks, length):
    return [prod(a - b*m for a, b in terms)
            for terms in combinations_with_replacement(marks, length)]


def divisors(value):
    small = []
    large = []
    for i in range(1, isqrt(value) + 1):
        if value % i == 0:
            small.append(i)
            if value != i*i:
                large.append(value // i)
    return small + large[::-1]


def check(height, low, high, length):
    marks = labels(height)
    tests = collisions = 0
    for m in range(low, high + 1):
        values = products(m, marks, length)
        assert len(set(map(abs, values))) == len(values)
        predicted = set()
        for j, u in enumerate(values):
            for v in values[:j]:
                for delta in (abs(u-v), abs(u+v)):
                    predicted.update(n for n in divisors(delta) if m*m <= n < (m+1)**2)
        direct = set()
        for n in range(m*m, (m+1)**2):
            reduced = {min(u % n, (-u) % n) for u in values}
            if len(reduced) < len(values):
                direct.add(n)
        assert direct == predicted
        if length == 1:
            assert 2*height*(m+1) < m*m and 2*height < m and not direct
        tests += 2*m+1
        collisions += len(predicted)
    return tests, collisions


if __name__ == "__main__":
    for length, lo, hi in ((1, 12, 50), (2, 45, 63), (3, 135, 139)):
        print(length, check(2, lo, hi, length))
