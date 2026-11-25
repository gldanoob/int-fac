"""Small cyclic affine tests and complete partitions from verified order exponents."""

from cmath import exp
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm, pi, prod, sqrt


def inverse_prime_distribution(modulus, primes):
    weights = [F(0) for _ in range(modulus)]
    for r in primes:
        inv = pow(r, -1, modulus)
        for j in range(r):
            weights[j*inv % modulus] += F(1, r*len(primes))
    assert sum(weights) == 1
    return weights


def transform(values):
    n = len(values)
    roots = [exp(-2j*pi*x/n) for x in range(n)]
    return [sum(float(v)*roots[k*x % n] for x, v in enumerate(values))/n for k in range(n)]


def cyclic_checks():
    cases = modes = wrap = 0
    for n in (8, 16, 32):
        primes = (13, 17, 19, 23, 29, 31)
        mu = inverse_prime_distribution(n, primes)
        eps = n * max(map(abs, transform(mu)[1:]))
        for r in primes:
            inv = pow(r, -1, n)
            h = (r*inv-1)//n
            for k in range(1, n):
                v = k*h % r
                short = min(v, r-v)
                if short >= 2:
                    avg = sum(exp(2j*pi*k*(j*inv % n)/n) for j in range(r))/r
                    assert abs(avg) <= 1/(2*(short-1)) + 1e-12
                assert any((k+i*n) % r == 0 for i in (short, -short))
                modes += 1
        for phase, a, b in product(range(3), (0, 1, 2, 3), (1, 2, 4)):
            f = [F(((x*x+3*x+phase) % 7) - 3, 4) for x in range(n)]
            g = [F(1 if (x+phase) % 3 else -1, 2) for x in range(n)]
            h0 = [F(1+(x+phase) % 3, 3) for x in range(n)]
            h1 = [F(2 if x > n//3 else -1, 3) for x in range(n)]
            diff = sum((mu[y]-F(1, n))*h0[x]*h1[y]*f[(x+a*y) % n]*g[(x+b*y) % n]
                       for x in range(n) for y in range(n))/n
            rhs = (eps * sum(map(abs, transform(h0))) * sum(map(abs, transform(h1)))
                   * sqrt(float(sum(z*z for z in f)*sum(z*z for z in g)))/n)
            assert float(abs(diff)) <= rhs + 1e-11
            cases += 1
        for x, y in product(range(-n//8, n//8), range(-n//8, n//8)):
            for a in (0, 1, 2):
                val = (x+a*y+n//2) % n - n//2
                assert val == x+a*y
                wrap += 1
    return cases, modes, wrap


def order(n, base, exponent):
    v = 1
    for k in range(1, exponent+1):
        v = v*base % n
        if v == 1:
            return k
    raise AssertionError((n, base, exponent))


def partition_checks():
    primes = (3, 5, 7, 11, 13)
    bases = (17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79)
    done = unitary = separated = 0
    for support_size in (2, 3):
        for support in combinations(primes, support_size):
            for powers in product((1, 2), repeat=support_size):
                pure = [p**k for p, k in zip(support, powers)]
                n = prod(pure)
                exponent = lcm(*(z//p*(p-1) for z, p in zip(pure, support)))
                profiles = {p: [] for p in support}
                branches = {n}
                for index, base in enumerate(bases):
                    e = exponent * (1, 2, 9, 12)[index % 4]
                    odd = e // (e & -e)
                    for p in support:
                        local = order(p, base, p-1)
                        profiles[p].append((local & -local).bit_length()-1)
                    x = pow(base, odd, n)
                    while True:
                        factor = gcd(x-1, n)
                        assert gcd(factor, n//factor) == 1
                        unitary += 1
                        new = set()
                        for d in branches:
                            g = gcd(d, factor)
                            new.update(k for k in (g, d//g) if k > 1)
                        branches = new
                        if x == 1:
                            break
                        x = x*x % n
                    groups = {tuple(profile) for profile in profiles.values()}
                    predicted = {prod(pure[i] for i, p in enumerate(support)
                                      if tuple(profiles[p]) == profile) for profile in groups}
                    assert branches == predicted
                    separated += len(branches) == len(pure)
                assert branches == set(pure)
                done += 1
    return done, unitary, separated


if __name__ == "__main__":
    print("affine comparisons, prime-inverse modes, exact integer lifts", *cyclic_checks())
    print("complete inputs, unitary gcds, fully separating prefixes", *partition_checks())
