"""Replay the modular and valuation construction of the private smooth rows."""

from itertools import count, product
from math import factorial, gcd, prod
from pathlib import Path
import runpy

HERE = Path(__file__).parent
PLANTS = runpy.run_path(str(HERE / "cogentic-planted-norm-two.py"))
evaluate = PLANTS["evaluate"]
multiply = PLANTS["multiply"]
integer_root = PLANTS["BASE"]["integer_root"]
squarefree_factors = runpy.run_path(str(HERE / "cogentic-fixed-rank-audit.py"))["squarefree_factors"]


def crt(residues, moduli):
    modulus = prod(moduli)
    return sum(value * (modulus // q) * pow(modulus // q, -1, q)
               for value, q in zip(residues, moduli, strict=True)) % modulus


def quotient_mod(dividend, divisor, prime):
    dividend = [c % prime for c in dividend]
    quotient = []
    while len(dividend) >= len(divisor):
        leading = dividend[-1]
        quotient.append(leading)
        offset = len(dividend) - len(divisor)
        for k, c in enumerate(divisor[:-1]):
            dividend[offset+k] = (dividend[offset+k] - leading*c) % prime
        dividend.pop()
    assert not any(dividend)
    return quotient[::-1]


def rootless(prime, degree):
    return next([*coefficients, 1] for coefficients in product(range(prime), repeat=degree)
                if all(evaluate([*coefficients, 1], x) % prime for x in range(prime)))


def norm_representative(residues, modulus, primes, forced):
    moduli = [modulus, *(p*p for p in primes)]
    period = prod(moduli)
    residue = crt([2, *residues], moduli) or period
    q = period // forced
    assert residue % forced == 0 and gcd(residue // forced, q) == 1
    for z in range(32*q):
        candidate = residue + period*z
        factors = squarefree_factors(candidate // forced)
        if factors is not None:
            assert all(forced % p for p in factors) and candidate <= 32*period**2
            return candidate
    raise AssertionError("squarefree progression exhausted")


def build(n, h, r):
    cuts = tuple(range(0, 2*r, 2))
    degrees = (h+r, h+r+1)
    m = integer_root(n, h)
    m -= 1 - m % 2
    assert m > cuts[-1]
    primes = []
    for p in count(2*degrees[-1]+3):
        if squarefree_factors(p) == [p]:
            primes.append(p)
            if len(primes) == r:
                break
    for a in [*(m-t for t in cuts), *primes]:
        divisor = gcd(a, n)
        if divisor > 1:
            assert divisor < n
            return divisor
    p_poly = [1]
    for cut in cuts:
        p_poly = multiply(p_poly, [-cut, 1])
    units = []
    for k in range(r):
        unit = [1]
        for j, cut in enumerate(cuts):
            if j != k:
                unit = multiply(unit, [-cut, 1])
        units.append(unit)
    assert all(multiply(unit, [-cut, 1]) == p_poly for cut, unit in zip(cuts, units))
    derivative_values = [evaluate(unit, cut) for cut, unit in zip(cuts, units)]
    mod = 4 * 2**(r-1) * factorial(r-1)
    k_product = prod(primes)
    local = []
    for j, (p, cut) in enumerate(zip(primes, cuts)):
        quad, cubic = (rootless(p, d) for d in (2, 3))
        reductions = []
        for i, degree in enumerate(degrees):
            size = degree - (i == j % 2)
            reduction = cubic if size % 2 else [1]
            for _ in range(size // 2 - size % 2):
                reduction = [v % p for v in multiply(reduction, quad)]
            if i == j % 2:
                reduction = multiply(reduction, [-cut, 1])
            reductions.append(reduction)
        local.append(reductions)

    bases = []
    target_norms = []
    lift_modulus = 2*k_product
    for i, degree in enumerate(degrees):
        interpolation = [2] + [0]*(r-1)
        norms = []
        for k, cut in enumerate(cuts):
            residues = [evaluate(local[j][i], cut) % p or p for j, p in enumerate(primes)]
            forced = 2*primes[k] if i == k % 2 else 2
            value = norm_representative(residues, mod, primes, forced)
            norms.append(value)
            factor, remainder = divmod(value-2, derivative_values[k])
            assert remainder == 0
            for a, c in enumerate(units[k]):
                interpolation[a] += factor*c
        target_norms.append(norms)
        quotients = []
        for j, p in enumerate(primes):
            dividend = local[j][i].copy()
            for a, c in enumerate(interpolation):
                dividend[a] -= c
            quotients.append(quotient_mod(dividend, p_poly, p))
        q = [crt([0, *(row[a] for row in quotients)], [2, *primes]) for a in range(degree-r)] + [1]
        poly = multiply(q, p_poly)
        for a, c in enumerate(interpolation):
            poly[a] += c
        target = -evaluate(poly, m) * pow(lift_modulus*evaluate(p_poly, m), -1, n) % n
        for a in range(h-1):
            target, digit = divmod(target, m)
            q[a] += lift_modulus*digit
        q[h-1] += lift_modulus*target
        poly = multiply(q, p_poly)
        for a, c in enumerate(interpolation):
            poly[a] += c
        bases.append(poly)

    bump = multiply([-m, 1], p_poly)
    for shift in range(3):
        fields = [base.copy() for base in bases]
        for poly in fields:
            for a, c in enumerate(bump):
                poly[a] += 4*k_product*shift*c
        gcds = [gcd(evaluate([a*c for a, c in enumerate(poly) if a], m), n) for poly in fields]
        for divisor in gcds:
            if 1 < divisor < n:
                return divisor
        if gcds == [1, 1]:
            return m, fields, cuts, primes, target_norms, 32*(mod*k_product**2)**2
    raise AssertionError("three derivative lifts exhausted")


def run():
    cases = [(77, 2, 1), (11*1009, 2, 1), (2**61-1, 2, 1), (2**61-1, 4, 2),
             (2**127-1, 6, 3), (1000003*1000033, 4, 2), (2**127-1, 6, 2)]
    pair_count = divisor_count = mark_count = 0
    for n, h, r in cases:
        result = build(n, h, r)
        if isinstance(result, int):
            assert 1 < result < n and n % result == 0
            divisor_count += 1
            continue
        m, fields, cuts, primes, target_norms, bound = result
        all_factors = []
        for i, poly in enumerate(fields):
            assert len(poly) == h+r+i+1 and poly[-1] == 1 and poly[0] % 4 == 2
            assert all(c % 2 == 0 for c in poly[:-1]) and evaluate(poly, m) % n == 0
            derivative = [a*c for a, c in enumerate(poly) if a]
            assert gcd(evaluate(derivative, m), n) == 1
            factors = []
            for j, cut in enumerate(cuts):
                assert gcd(m-cut, n) == 1
                value = evaluate(poly, cut)
                assert value == target_norms[i][j] and 0 < value <= bound
                fs = squarefree_factors(value)
                assert fs is not None and fs[0] == 2 and prod(fs) == value
                factors.append(fs)
            all_factors.append(factors)
            for j, p in enumerate(primes):
                roots = [x for x in range(p) if evaluate(poly, x) % p == 0]
                assert roots == ([cuts[j]] if i == j % 2 else [])
                if roots:
                    assert evaluate(derivative, roots[0]) % p != 0
        for j, p in enumerate(primes):
            assert [(i, k) for i, row in enumerate(all_factors) for k, fs in enumerate(row) if p in fs] == [(j % 2, j)]
        pair_count += 1
        mark_count += r
    assert pair_count == 5 and divisor_count == 2 and mark_count == 10
    print(f"{pair_count} field pairs, {divisor_count} proper divisors, {mark_count} squarefree marks and private ideal rows")


if __name__ == "__main__":
    run()
