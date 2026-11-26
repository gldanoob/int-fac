"""Exact multiband schedule, endpoint checks, and a small prefix-count replay."""
from fractions import Fraction as F
from itertools import product
from math import prod

stages = 128
v0 = F(143, 200)
v = [v0+(1-v0)*j/(stages-1) for j in range(stages)]
a = [value**2 for value in v]
h = F(70277, 50000)
weights = [h*(right-left) for left, right in zip(v, v[1:])]
weights.append(F(9, 20)-sum(x*w for x, w in zip(a, weights)))
fractions = [x*w/F(9, 20) for x, w in zip(a, weights)]
b, slack = F(19, 20), F(1, 10000)
target = F(251, 100)
assert min(weights) > 0 and sum(fractions) == 1
assert F(51, 100) < F(5108, 10000) < a[0] < a[-1] == 1
assert F(20001, 10000)**2*F(40, 81) < h*h
assert sum(f/x for f, x in zip(fractions, a)) < 2
costs = [b+sum(weights[j:])+h*v[j]+slack for j in range(stages)]
assert len(set(costs)) == 1 and max(costs) < target
s_a, s_r = F(43, 40), F(5926, 12255)
raw = b+s_a+s_r+2*slack
alg_before_test = b+s_a+2*slack
h1_squared = (F(20001, 20100)**2)*F(76313, 322500)
assert raw < target and (target-alg_before_test)**2 > h1_squared
assert b*F(26, 10) < target
print(f"private stages {float(max(costs)):.10f}, raw {float(raw):.10f}, "
      f"algebraic {float(alg_before_test)+float(h1_squared)**.5:.10f}")


def band_part(value, primes):
    part = 1
    for p in primes:
        while value % p == 0:
            value //= p
            part *= p
    return part


def replay():
    bands = [(2, 3), (5, 7), (11, 13)]
    thresholds = [4, 5, 11]
    width = 512
    active = set(range(1, width+1))
    divisors = []
    for band, threshold in zip(bands, thresholds):
        active = {v for v in active if band_part(v, band) >= threshold}
        divisors.append([d for d in range(threshold, width+1)
                         if band_part(d, band) == d])
        # Each survivor is a multiple of a product of coprime certified band parts.
        cover = sum(width//prod(ds) for ds in product(*divisors))
        assert len(active) <= cover
        print(f"prefix {len(divisors)}: {len(active)} survivors, {cover} divisor witnesses")
    assert active


if __name__ == "__main__":
    replay()
