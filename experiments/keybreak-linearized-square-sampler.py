"""Sample a short modular square root with affine windows and Euclidean floor sums."""
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt
from secrets import randbelow


def floor_sum(count, modulus, slope, intercept):
    """Sum floor((slope*i + intercept) / modulus) over 0 <= i < count."""
    total = 0
    while count:
        quotient, slope = divmod(slope, modulus)
        total += quotient * count * (count - 1) // 2
        quotient, intercept = divmod(intercept, modulus)
        total += quotient * count
        height = slope * count + intercept
        if height < modulus:
            break
        count, intercept = divmod(height, modulus)
        modulus, slope = slope, modulus
    return total


def linear_hit_count(n, x, width, center, count):
    """Count offsets before count whose linearized square lies in [-width², x]."""
    slope, square = 2 * center, center * center
    return (floor_sum(count, n, slope, square + width**2)
            - floor_sum(count, n, slope, square - x - 1))


def proposed_root(n, x, center, slot):
    """One fixed proposal. None is an empty, excess, nonunit, or false-positive slot."""
    width = isqrt(x)
    assert 0 < x < n and width**2 + x + 1 <= n
    slots = (4 * width * x + n - 1) // n
    assert 0 <= center < n and 0 <= slot < slots
    hits = linear_hit_count(n, x, width, center, width)
    if hits > slots or slot >= hits:
        return None
    low, high = 0, width
    while low + 1 < high:
        mid = (low + high) // 2
        if linear_hit_count(n, x, width, center, mid) > slot:
            high = mid
        else:
            low = mid
    z = (center + high - 1) % n
    if gcd(z, n) == 1 and 1 <= z*z % n <= x:
        return z
    return None


def sample(n, x, draw=randbelow):
    """One raw trial, using independent uniform integer draws."""
    slots = (4 * isqrt(x) * x + n - 1) // n
    return proposed_root(n, x, draw(n), draw(slots))


def check():
    for n in range(1, 13):
        for m in range(1, 13):
            for a in range(-4, 13):
                for b in (-29, -1, 0, 6, 31):
                    assert floor_sum(n, m, a, b) == sum((a*i + b)//m for i in range(n))
    for n, x in ((63, 23), (105, 42), (169, 50), (255, 91), (501, 60), (501, 158), (1021, 100), (1021, 300)):
        width = isqrt(x)
        slots = (4*width*x + n-1)//n
        counts, expected = Counter(), Counter()
        roots = [z for z in range(n) if gcd(z, n) == 1 and 1 <= z*z % n <= x]
        for center in range(n):
            linear = [(center**2 + 2*center*r) % n for r in range(width)]
            hits = [r for r, v in enumerate(linear) if v <= x or v >= n-width**2]
            assert len(hits) == linear_hit_count(n, x, width, center, width)
            if len(hits) <= slots:
                for r in hits:
                    z = (center + r) % n
                    if z in roots:
                        expected[z] += 1
            for slot in range(slots):
                z = proposed_root(n, x, center, slot)
                if z is not None:
                    counts[z] += 1
        assert counts == expected and max(counts.values()) <= width
        mass = counts.total()
        tv = sum(abs(Fraction(counts[z], mass) - Fraction(1, len(roots))) for z in roots)/2
        assert tv <= Fraction(sum(counts[z] < width for z in roots), len(roots))
        print(f"N={n}, X={x}, roots={len(roots)}, acceptance={mass/(n*slots):.3f}, TV={float(tv):.4f}")


if __name__ == "__main__":
    check()
